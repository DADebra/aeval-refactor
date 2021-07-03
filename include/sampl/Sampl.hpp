#ifndef SAMPL__HPP__
#define SAMPL__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"
#include "BoolCom.hpp"
#include "ArrCom.hpp"

#include <fstream>
#include <cctype>
#include <regex>

using namespace std;
using namespace boost;

namespace ufo
{
  // wrapper for LinCom.hpp, BoolCom.hpp, etc (in the future)
  class Sampl
  {
    public:

    Bdisj b_part;
    LAdisj l_part;

    int arity()
    {
      return l_part.arity + ((b_part.arity > 0) ? 1 : 0);
    }

    bool empty() { return arity() == 0; }

    Sampl() {}

  };

  class SamplFactory
  {
    private:
    ExprFactory &m_efac;

    EZ3 &z3;

    vector<Sampl> samples;

    density hasBooleanComb;
    density orAritiesDensity;
    bool hasArrays = false;

    // Previously generated candidates from sample grammar
    unordered_set<Expr> gramCands;

    // Key: Non-terminal, Value: Productions in b/ieither# format
    std::map<Expr, Expr> defs;

    // The root of the tree of the grammar
    Expr inv;

    // The file location of the grammar SMT2 file
    string gram_file;

    // All variables mentioned in the file, regardless of type.
    // Variables are for the invariant stored in 'inv'
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprVector> inv_vars;

    // Variables for the other invariants in the input file.
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprVector> other_inv_vars;

    // Whether to print debugging information or not
    bool printLog;

    public:

    LAfactory lf;
    Bfactory bf;
    ARRfactory af;

    ExprSet learnedExprs;

    bool initilized = true;

    SamplFactory(ExprFactory &_efac, EZ3 &_z3, bool aggp, bool _printLog, 
        string grammar) :
      m_efac(_efac), z3(_z3), lf(_efac, aggp), bf(_efac), af(_efac, aggp),
      gram_file(grammar), printLog(_printLog), inv(NULL) {}

    // Parse the grammar file. Must be called after addVar(s)
    void initialize_gram(string inv_fname)
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

        // Generate enough eithers for INT_CONSTS
        eithers_to_gen.insert(lf.getConsts().size());

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
          if (printLog) outs() << "Found either_" << eithermatch[1] << endl;
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
        auto generate_all = [&] (unordered_map<Expr, ExprVector> vars, 
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
              if (pair.second.size() != 1)
              {
                aug_gram << "(assert (= " << vars_name << 
                  " (" << sort_name << "_either_" << pair.second.size();

                for (auto& var : pair.second)
                {
                  aug_gram << " " << var;
                }

                aug_gram << ")))" << endl;
              }
              else
              {
                aug_gram << "(assert (= " << vars_name << " " << pair.second[0] <<
                  "))" << endl;
              }
            }
          }
        };

        generate_all(inv_vars, true);
        generate_all(other_inv_vars, false);

        // Generate INT_CONSTS definition
        aug_gram << "(declare-fun INT_CONSTS () Int)" << endl;

        if (lf.getConsts().size() != 0)
        {
          aug_gram << "(assert (= INT_CONSTS ";
          aug_gram << "(Int_either_" << lf.getConsts().size() << " ";
          for (auto& c : lf.getConsts())
          {
            aug_gram << c << " ";
          }
          aug_gram << ")))" << endl;
        }

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
            if (ex_fname == "ANY_INV" && inv == NULL)
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

      if (printLog)
      {
        if (inv == NULL) outs() << "Using built-in grammar." << endl;
        else outs() << "Using user-provided grammar(s)." << endl;
      }
    }

    Expr getAllLemmas()
    {
      return conjoin(learnedExprs, m_efac);
    }

    // Add variable for this invariant
    bool addVar(Expr var)
    {
      bool added = false;
      if (bind::isBoolConst(var))
      {
        bf.addVar(var);
        added = true;
      }
      else if (bind::isIntConst(var))
      {
        lf.addVar(var);
        added = true;
      }
      else if (bind::isConst<ARRAY_TY> (var))
      {
        af.addVar(var);
        added = true;
        hasArrays = true;
      }

      inv_vars[bind::typeOf(var)].push_back(var);
      added = true;

      return added;
    }

    // Add variable for other invariants
    void addOtherVar(Expr var)
    {
      other_inv_vars[bind::typeOf(var)].push_back(var);
    }

    void initialize(ExprSet& arrCands, ExprVector& arrAccessVars, ExprSet& arrRange)
    {
      bf.initialize();
      lf.initialize();
      if (hasArrays)
      {
        if (arrAccessVars.empty() || arrRange.empty())
        {
          initilized = false;
        }
        else
        {
          af.initialize(lf.getVars(), arrCands, arrAccessVars, arrRange);
        }
      }
    }

    Sampl& exprToSampl(Expr ex)
    {
      samples.push_back(Sampl());
      Bdisj& bcs = samples.back().b_part;
      LAdisj& lcs = samples.back().l_part;

      bf.exprToBdisj(ex, bcs);
      lf.exprToLAdisj(ex, lcs);

      if (!lcs.empty()) lcs.normalizePlus();
      if (!bcs.empty()) bcs.normalizeOr();

      return samples.back();
    }

    Expr sampleToExpr(Sampl& s)
    {
      if (s.l_part.arity == 0 && s.b_part.arity == 0)
        return NULL;
      if (s.l_part.arity == 0)
        return bf.toExpr(s.b_part);
      if (s.b_part.arity == 0)
        return lf.toExpr(s.l_part);

      return mk<OR>(bf.toExpr(s.b_part), lf.toExpr(s.l_part));
    }

    void calculateStatistics(bool freqs, bool addepsilon)
    {
      int maxArity = 0;
      set<int> orArities;

      if (lf.getVars().size() > 0 && samples.size() == 0)
      {
        // artificially add one default sample in case there is nothing here
        // TODO: find a better solution
        exprToSampl (mk<GEQ>(lf.getVars()[0], mkTerm (mpz_class (0), m_efac)));
      }

      for (auto &s : samples)
      {
        maxArity = max (maxArity, s.arity());
        orArities.insert(s.arity());
        orAritiesDensity[s.arity()] ++;
      }

      for (int i = 0; i < maxArity; i++)
      {
        if (orAritiesDensity[i] == 0)
          orArities.insert(i);
      }

      lf.initDensities(orArities);
      bf.initDensities();

      for (auto &s : samples)
      {
        LAdisj& l = s.l_part;
        Bdisj& b = s.b_part;
        if (!l.empty())
        {
          lf.calculateStatistics(l, s.arity(), freqs, addepsilon);
        }
        if (!b.empty())
        {
          bf.calculateStatistics(b, freqs);
          hasBooleanComb[1]++;
        }
        else
        {
          // frequency of empty bool combinations
          hasBooleanComb[0]++;
        }
      }

      // now, stabilization:

      if (!freqs)
      {
        for (auto & ar : orAritiesDensity)
        {
          ar.second = 1;
        }
      }

      bf.stabilizeDensities(addepsilon, freqs);

      for (auto & ar : orAritiesDensity)
      {
        lf.stabilizeDensities(ar.first, addepsilon, freqs);
      }
    }

    // qvars is set of quantifier variables for this expression.
    // Using pointer because we need it to be nullable.
    Expr getRandCand(Expr root, unordered_set<Expr> *qvars)
    {
      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        if (fname.find("_FH_") != fname.npos)
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
              ". Exiting." << endl;
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
      unordered_set<Expr> localqvars;

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

    Expr getFreshCandidate(bool arrSimpl = true)
    {
      // If we weren't provided a grammar on the command line, then
      // inv will be NULL.
      if (inv != NULL)
      {
        Expr randcand;

        while (true)
        {
          // Generate a (possibly old) candidate from the grammar,
          // and simplify
          randcand = simplifyBool(simplifyArithm(getRandCand(inv, NULL)));
          auto ret = gramCands.insert(randcand);
          if (ret.second)
            // We generated a new candidate, so return to caller.
            break;

          // Else, we generated an existing grammar. Try again.
        }

        // We return 'false' and 'true' once, but since they get added
        // to gramCands we never return them again.
        // Thus, we don't bother checking for them.
        return randcand;
      }

      // for now, if a CHC system has arrays, we try candidates only with array
      // in the future, we will need arithmetic candidates as well
      if (hasArrays && initilized)
      {
        Expr cand = arrSimpl ? af.guessSimplTerm() : af.guessTerm();
        if (cand != NULL)
        {
          for (auto & v : lf.nonlinVars) cand = replaceAll(cand, v.second, v.first);
          return cand;
        }
      }

      if (orAritiesDensity.empty()) return NULL;

      int arity = chooseByWeight(orAritiesDensity);
      int hasBool = chooseByWeight(hasBooleanComb);
      int hasLin = arity - hasBool;
      samples.push_back(Sampl());
      Sampl& curCand = samples.back();

      Expr lExpr;
      if (hasLin > 0)
      {
        if (!lf.guessTerm(curCand.l_part, arity, hasLin)) return NULL;
        curCand.l_part.normalizePlus();
        lExpr = lf.toExpr(curCand.l_part);
      }

      Expr bExpr;
      if (hasBool > 0)
      {
        if (!bf.guessTerm(curCand.b_part)) return NULL;
        bExpr = bf.toExpr(curCand.b_part);
      }

      if (hasBool > 0 && hasLin > 0)
      {
        return mk<OR>(bExpr, lExpr);
      }
      else if (hasBool > 0)
      {
        return bExpr;
      }
      else
      {
        return lExpr;
      }
    }

    void assignPrioritiesForLearned(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForLearned(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForFailed(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForFailed(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForBlocked(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForBlocked(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForLearned()
    {
      assignPrioritiesForLearned(samples.back());
    }

    void assignPrioritiesForFailed()
    {
      assignPrioritiesForFailed(samples.back());
    }

    void assignPrioritiesForBlocked()
    {
      assignPrioritiesForBlocked(samples.back());
    }

    void printStatistics()
    {
      for (auto &a : orAritiesDensity)
      {
        outs() << "OR arity density: " << a.first << " |--> " << a.second << "\n";
      }

      bf.printCodeStatistics();

      if (lf.getConsts().size() > 0)
      {
        outs() << "\nInt consts:\n";
        for (auto &form: lf.getConsts()) outs() << lexical_cast<string>(form) << ", ";
        outs() << "\b\b \n";

        for (auto &ar : orAritiesDensity) lf.printCodeStatistics(ar.first);
      }
    }
  };
}

#endif
