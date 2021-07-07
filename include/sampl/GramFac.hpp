#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"

#include <fstream>
#include <cctype>
#include <regex>
#include <tuple>

#include <boost/coroutine2/coroutine.hpp>

using namespace std;
using namespace boost;
using namespace boost::coroutines2;

namespace ufo
{
  const char* ANY_INV = "ANY_INV";
  const char* INT_CONSTS = "INT_CONSTS";

  typedef unordered_set<Expr> ExprUSet;
  typedef unordered_map<Expr, Expr> ExprUMap;

  // Candidate generation method.
  //   RND - Completely random candidate without replacement.
  //   TRAV - Traverse full grammar up to specified depth.
  enum class GramGenMethod { RND, TRAV };

  // Parameters for generation using grammar.
  //   1st - GramGenMethod
  //   2nd - Maximum recursion depth
  typedef std::tuple<GramGenMethod, int> GramParams;

  class GRAMfactory
  {
    private:

    // A coroutine returning an Expr.
    typedef coroutine<Expr>::pull_type ExprCoro;

    // The main coroutine we use to traverse the grammar.
    std::unique_ptr<ExprCoro> getNextCandTrav;

    // Needed for candidate generation.
    ExprFactory &m_efac;

    // Needed for parsing grammar.
    EZ3 &z3;

    // Previously generated candidates from sample grammar
    ExprUSet gramCands;

    // Key: Non-terminal, Value: Productions in b/ieither# format
    ExprUMap defs;

    // The root of the tree of the grammar
    Expr inv;

    // All variables mentioned in the file, regardless of type.
    // Variables are for the invariant stored in 'inv'
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprUSet> inv_vars;

    // Variables for the other invariants in the input file.
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprUSet> other_inv_vars;

    // Set of integer constants that appear in the program.
    ExprUSet int_consts;

    // Whether to print debugging information or not.
    bool printLog;

    /*** PARAMETERS (respective to GramParams) ***/

    // How this GRAMfactory will generate candidates.
    GramGenMethod genmethod;

    // The maximum recursion depth during traversal.
    int maxrecdepth;

    public:

    bool initialized = false;

    private:

    // exp is e.g. (= iterm iterm), nonterm is e.g. iterm
    bool isRecursive(Expr exp, Expr nonterm)
    {
      for (auto itr = exp->args_begin(); itr != exp->args_end(); ++itr)
      {
        if (*itr == nonterm)
          return true;
      }
      // Handle simple recursion
      if (exp == nonterm)
        return true;

      return false;
    }

    void getNextCandTrav_fn(coroutine<Expr>::push_type &sink, Expr root = NULL,
        int currdepth = 0, ExprUSet *qvars = NULL, Expr currnt = NULL)
    {
      if (root == NULL)
        root = inv;

      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const ExprUSet &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          sink(root);
          return;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname.find("either") != string::npos)
        {
          // Randomly select from the available productions.
          vector<int> order;
          set<int> done;
          while (done.size() < root->arity() - 1)
          {
            // Offset by 1 because arg(0) is the fdecl.
            int randnum = (rand() % (root->arity() - 1)) + 1;

            if (!done.insert(randnum).second)
              continue;

            // Don't traverse past maximum depth
            if (!isRecursive(root->arg(randnum), currnt) ||
            currdepth + 1 <= maxrecdepth)
              order.push_back(randnum);
          }

          for (int i : order)
          {
            int newdepth;
            if (isRecursive(root->arg(i), currnt))
              newdepth = currdepth + 1;
            else
              newdepth = currdepth;

            for (Expr exp : getCandCoro(root->arg(i), newdepth, qvars, currnt))
              sink(exp);
          }
          return;
        }
        else
        {
          // Root is user-defined non-terminal
          if (defs[root] != NULL)
          {
            for (Expr exp : getCandCoro(defs[root], root == currnt ? currdepth : 0, qvars, root))
              sink(exp);
            return;
          }
          else if (qvars != NULL &&
          qvars->find(root->first()) != qvars->end())
          {
              // Root is a variable for a surrounding quantifier
              sink(root);
              return;
          }
          else
          {
            // There's no definition, we're expanding an empty *_VARS
            outs() << "ERROR: There is no definition for user-defined " <<
              "non-terminal " << root << " in the CFG for " << inv <<
              ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
            exit(1);
          }
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        sink(root);
        return;
      }

      // Root is Z3-defined non-terminal

      ExprUSet localqvars;

      if (qvars != NULL)
        for (auto& var : *qvars)
          localqvars.insert(var);

      if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      {
        // Add quantifier variables to qvars
        for (int i = 0; i < root->arity() - 1; ++i)
        {
          localqvars.insert(root->arg(i));
        }
      }

      // The set of Expr's we'll use to generate this n-ary expression.
      ExprVector expanded_args;
      // The corresponding coroutines for each entry in expanded_args.
      vector<ExprCoro> argcoros;

      // Initialize all arguments to valid Expr's;
      //   otherwise we can't do mkNary below.
      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
      {
        argcoros.push_back(getCandCoro(*itr, currdepth, &localqvars, currnt));
        expanded_args.push_back(argcoros.back().get());
        argcoros.back()();
      }

      // We just generated the first candidate; sink it.
      sink(m_efac.mkNary(root->op(), expanded_args));

      for (int x = 0; x < argcoros.size(); ++x)
      {
        ExprCoro &corox = argcoros[x];
        for (Expr expx : corox)
        {
          expanded_args[x] = expx;

          if (x == 0)
            // If x == 0, then bottom for loop never runs and we never sink.
            sink(m_efac.mkNary(root->op(), expanded_args));

          for (int y = 0; y < x; ++y)
          {
            ExprCoro &coroy = argcoros[y];
            if (!coroy)
              coroy = getCandCoro(root->arg(y), currdepth, &localqvars, currnt);
            for (Expr expy : coroy)
            {
              expanded_args[y] = expy;
              sink(m_efac.mkNary(root->op(), expanded_args));
            }
          }
        }
      }

      // Traversal of root done.
      return;
    }
    ExprCoro getCandCoro(Expr root = NULL, int currdepth = 0,
      ExprUSet *qvars = NULL, Expr currnt = NULL)
    {
      return std::move(ExprCoro(std::bind(&GRAMfactory::getNextCandTrav_fn, this,
            std::placeholders::_1, root, currdepth, qvars, currnt)));
    }

    // qvars is set of quantifier variables for this expression.
    // Using pointer because we need it to be nullable.
    Expr getRandCand(Expr root, ExprUSet *qvars = NULL)
    {
      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const ExprUSet &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          return root;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname.find("either") != string::npos)
        {
          Expr cand = NULL;
          while (cand == NULL)
          {
            // Randomly select from the available productions.
            // Offset by 1 because arg(0) is the fdecl.
            int randindex = (rand() % (root->arity() - 1)) + 1;

            cand = getRandCand(root->arg(randindex), qvars);
            return cand;
          }
        }
        else
        {
          // Root is user-defined non-terminal
          if (defs[root] != NULL)
            return getRandCand(defs[root], qvars);
          else if (qvars != NULL &&
           qvars->find(root->first()) != qvars->end())
            // Root is a variable for a surrounding quantifier
            return root;
          else
          {
            // There's no definition, we're expanding an empty *_VARS
            outs() << "ERROR: There is no definition for user-defined " <<
              "non-terminal " << root << " in the CFG for " << inv <<
              ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
            exit(1);
            // We never get here
            return NULL;
          }
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        return root;
      }

      // Root is Z3-defined non-terminal

      ExprVector expanded_args;
      ExprUSet localqvars;

      if (qvars != NULL)
        for (auto& var : *qvars)
          localqvars.insert(var);

      if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      {
        // Add quantifier variables to qvars
        for (int i = 0; i < root->arity() - 1; ++i)
        {
          localqvars.insert(root->arg(i));
        }
      }

      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
        expanded_args.push_back(getRandCand(*itr, &localqvars));

      // Don't generate undefined candidates (e.g. mod by 0)
      if (isOpX<MOD>(root) || isOpX<DIV>(root) || isOpX<IDIV>(root))
      {
        while (isOpX<MPZ>(expanded_args.back()) && lexical_cast<cpp_int>(expanded_args.back()) <= 0)
          expanded_args.back() = getRandCand(root->last(), qvars);
      }

      return m_efac.mkNary(root->op(), expanded_args);
    }

    public:

    GRAMfactory(ExprFactory &_efac, EZ3 &_z3, bool _printLog) :
      m_efac(_efac), z3(_z3), printLog(_printLog), inv(NULL),
      getNextCandTrav(nullptr) {}

    void addVar(Expr var)
    {
      inv_vars[bind::typeOf(var)].insert(var);
    }

    void addOtherVar(Expr var)
    {
      other_inv_vars[bind::typeOf(var)].insert(var);
    }

    void addIntConst(cpp_int iconst)
    {
      int_consts.insert(mkMPZ(iconst, m_efac));
    }

    void setParams(GramParams params)
    {
      std::tie(genmethod, maxrecdepth) = params;
    }

    GramParams getParams()
    {
      return std::move(std::make_tuple(genmethod, maxrecdepth));
    }

    // Parse the grammar file. Must be called after addVar(s).
    void initialize(string gram_file, string inv_fname)
    {
      // gram_file will be empty if we don't pass `--grammar` option
      if (!gram_file.empty())
      {
        // Read in entire user grammar
        ostringstream user_cfg;
        ifstream infile(gram_file);
        user_cfg << infile.rdbuf();

        // The set of eithers we need to generate.
        // Not worth making a distinction between sorts.
        unordered_set<int> eithers_to_gen;

        // Generate enough eithers for *_VARS
        for (auto& pair : inv_vars)
        {
          eithers_to_gen.insert(pair.second.size());
        }

        // Generate the eithers the user CFG uses.
        smatch eithermatch;
        regex eitherregex("either_([0-9]+)");
        string searchstr = user_cfg.str();

        while (regex_search(searchstr, eithermatch, eitherregex))
        {
          eithers_to_gen.insert(stoi(eithermatch[1]));
          searchstr = eithermatch.suffix().str();
        }

        // The provided grammar, plus variable definitions and special
        //   variables that we define.
        ostringstream aug_gram;

        auto generate_either_decl = [&] (string sort_name, string sort_smt)
        {
            // Generate either functions for given sort
            for (auto& i : eithers_to_gen)
            {
              aug_gram << "(declare-fun " << sort_name << "_either_" << i << " (";
              for (int x = 1; x <= i; ++x)
              {
                aug_gram << sort_smt << " ";
              }
              aug_gram << ") " << sort_smt << ")\n";
            }
        };

        // We need the Bool eithers for the inv definition (rel is Bool)
        aug_gram << "(declare-fun BOOL_VARS () Bool)" << endl;
        generate_either_decl("Bool", "Bool");

        // Which sorts we've already generated eithers and *_VARS for.
        ExprSet donesorts;
        donesorts.insert(mk<BOOL_TY>(m_efac));

        // Easiest way to handle all_inv_vars and inv_vars
        auto generate_all = [&] (unordered_map<Expr, ExprUSet> vars,
            bool thisinv)
        {
          for (auto& pair : vars)
          {
            string sort_smt = z3_to_smtlib<EZ3>(z3, pair.first);

            string sort_name(sort_smt);

            if (sort_name.find("(") != string::npos)
            {
              // We have a parameterized sort (e.g. Array)
              for (auto&c : sort_name)
              {
                if (c == '(' || c == ')')
                  c = '$';
                else if (c == ' ')
                  c = '_';
              }
            }

            // Generate special variable for this sort
            string vars_name(sort_name);
              vars_name += "_VARS";
            for (auto& c : vars_name)
              c = (char)toupper(c);

            // If we haven't already generated an either
            if (donesorts.find(pair.first) == donesorts.end())
            {
              aug_gram << "(declare-fun " << vars_name << " () " << sort_smt << ")\n";

              generate_either_decl(sort_name, sort_smt);
              donesorts.insert(pair.first);
            }

            // Generate _FH_* decls for this sort
            for (auto& var : pair.second)
            {
              // var is a FAPP
              aug_gram << z3_to_smtlib(z3, bind::fname(var)) << endl;
            }

            // Only generate definitions for variables of this SamplFactory's invariant
            if (thisinv)
            {
              // Generate definition (i.e. productions) for this sort's *_VARS
              if (pair.second.size() >= 1)
              {
                aug_gram << "(assert (= " << vars_name <<
                  " (" << sort_name << "_either_" << pair.second.size();

                for (auto& var : pair.second)
                {
                  aug_gram << " " << var;
                }

                aug_gram << ")))" << endl;
              }
              else if (pair.second.size() == 1)
              {
                aug_gram << "(assert (= " << vars_name << " " << *pair.second.begin() <<
                  "))" << endl;
              }
            }
          }
        };

        generate_all(inv_vars, true);
        generate_all(other_inv_vars, false);

        // Generate INT_CONSTS declaration
        aug_gram << "(declare-fun " << INT_CONSTS << " () Int)" << endl;

        aug_gram << user_cfg.str();

        if (printLog)
        {
          outs() << ";Provided user grammar: " << endl;
          outs() << aug_gram.str() << endl << endl;
        }

        // Parse combined grammar
        Expr gram = z3_from_smtlib<EZ3>(z3, aug_gram.str());

        // Find root of grammar and fill in `defs` map.
        for (auto iter = gram->args_begin(); iter != gram->args_end(); ++iter)
        {
          //ex is an assertion
          Expr ex = *iter;
          if (isOpX<EQ>(ex))
          {
            string ex_fname = lexical_cast<string>(bind::fname(ex->left())->left());
            if (ex_fname == ANY_INV && inv == NULL)
            {
              // Only use ANY_INV if we don't already have a specific one
              inv = ex->left();
            }
            else if (ex_fname == inv_fname)
            {
              inv = ex->left();
            }

            defs[ex->left()] = ex->right();
          }
        }
      }

      initialized = (inv != NULL);

      if (printLog)
      {
        if (initialized)
          outs() << "Using user-provided grammar(s)." << endl;
        else
          outs() << "Using built-in grammar." << endl;
      }
    }

    // Properly initialize INT_CONSTS now that we've found them
    void initialize_intconsts()
    {
      if (int_consts.size() != 0)
      {
        Expr eitherfunc = bind::fdecl(mkTerm(string("Int_either_") + to_string(int_consts.size()), m_efac),
            ExprVector(int_consts.size(), m_efac.mkTerm(INT_TY())));

        Expr int_consts_decl = bind::intConst(mkTerm(string(INT_CONSTS), m_efac));
        defs[int_consts_decl] = bind::fapp(eitherfunc, int_consts);
      }

      if (initialized && genmethod == GramGenMethod::TRAV)
      {
        ExprUSet *qvars = NULL;
        int currdepth = 0;
        Expr currnt = NULL;
        getNextCandTrav = std::unique_ptr<ExprCoro>(new ExprCoro(
            std::bind(&GRAMfactory::getNextCandTrav_fn, this,
            std::placeholders::_1, inv, currdepth, qvars, currnt)));
      }
    }

    Expr getFreshCandidate()
    {
      if (inv == NULL)
        return NULL; // Should never happen, but handle just in case

      Expr randcand;

      switch (genmethod)
      {
        case GramGenMethod::TRAV:
          // Generate a (possibly old) candidate from the grammar,
          // and simplify
          if (!*getNextCandTrav)
          {
            outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
            exit(0);
            return NULL;
          }
          randcand = simplifyBool(simplifyArithm(getNextCandTrav->get()));
          (*getNextCandTrav)();
          return randcand;
        case GramGenMethod::RND:
          /*while (true)
          {*/
            randcand = simplifyBool(simplifyArithm(getRandCand(inv)));
            /*auto ret = gramCands.insert(randcand);
            if (ret.second)
              // Candidate is new
              break;
          }*/
          return randcand;
      }

      // Should never happen.
      return NULL;
    }
  };

  class CFGUtils
  {
    public:

    // Returns the path to the CFG (within 'grams') corresponding to invDecl.
    // Returns the empty string if no appropriate CFG is found.
    // Set 'useany' to only look for ANY_INV.
    static string findGram(vector<string>& grams, Expr invDecl,
        bool useany = false)
    {
      string invName = lexical_cast<string>(invDecl->left());

      // The declarations in the grammar we're looking for.
      // Note: a (declare-rel) won't work, so we don't need to look for it.
      string finddecl1 = "(declare-fun " + invName + " () Bool)";
      string finddecl2 = "(declare-var " + invName + " Bool)";
      string finddecl3 = string("(declare-fun ") + ANY_INV + " () Bool)";
      string finddecl4 = string("(declare-var ") + ANY_INV + " Bool)";

      for (auto& gramstr : grams)
      {
        ifstream gramfile(gramstr);
        string line;
        while (getline(gramfile, line))
        {
          if (!useany)
          {
            // Prioritize the exact invariant decl over ANY_INV
            if (line.find(finddecl1) != string::npos ||
              line.find(finddecl2) != string::npos)
            {
              gramfile.close();
              return gramstr;
            }
          }
          else
          {
            if (line.find(finddecl3) != string::npos ||
              line.find(finddecl4) != string::npos)
            {
              gramfile.close();
              return gramstr;
            }
          }
        }
      }

      if (!useany)
      {
        // Retry, looking for ANY_INV this time.
        return std::move(findGram(grams, invDecl, true));
      }
      else
      {
        // We've exhausted the list of grammars, return failure.
        return "";
      }
    }

    static GramGenMethod strtogenmethod(const char* methodstr)
    {
      if (!strcmp(methodstr, "rnd"))
        return GramGenMethod::RND;
      if (!strcmp(methodstr, "traverse"))
        return GramGenMethod::TRAV;

      return GramGenMethod::RND;
    }
  };
}

#endif
