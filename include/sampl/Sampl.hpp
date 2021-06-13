#ifndef SAMPL__HPP__
#define SAMPL__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"
#include "BoolCom.hpp"
#include "ArrCom.hpp"

#include <fstream>
#include <cctype>

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
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprVector> all_vars;

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
    void initialize_gram(Expr invDecl)
    {
      // Maximum number of arguments for generated either functions
      int eithersize = 10; 

      // Generate enough eithers for INT_CONSTS
      eithersize = eithersize > lf.getConsts().size() ? eithersize :
        lf.getConsts().size();

      // Generate enough eithers for *_VARS
      int largestnumvars = 0;
      for (auto& pair : all_vars)
      {
        if (pair.second.size() > largestnumvars)
          largestnumvars = pair.second.size();
      }

      eithersize = eithersize > largestnumvars ? eithersize : largestnumvars;

      // The name of the invariant in invDecl
      string inv_fname = lexical_cast<string>(invDecl->left());

      // gram_file will be empty if we don't pass `--grammar` option
      if (!gram_file.empty())
      {
        // The provided grammar, plus variable definitions and special
        //   variables that we define.
        ostringstream aug_gram;

        auto generate_eithers = [&] (string sort_name, string sort_smt) {
            // Generate either functions for given sort
            for (int i = 2; i <= eithersize; ++i)
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
        generate_eithers("Bool", "Bool");

        aug_gram << "(declare-fun ANY_INT () Int)\n";

        for (auto& pair : all_vars)
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

          aug_gram << "(declare-fun " << vars_name << " () " << sort_smt << ")\n";

          // We already generated either functions for Bool
          if (sort_name != "Bool")
          {
            generate_eithers(sort_name, sort_smt);
          }

          // Generate _FH_* decls for this sort
          for (auto& var : pair.second)
          {
            // var is a FAPP
            aug_gram << z3_to_smtlib(z3, bind::fname(var)) << endl;
          }

          // Generate definition (i.e. productions) for this sort
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

        // Generate INT_CONSTS definition
        aug_gram << "(declare-fun INT_CONSTS () Int)" << endl;

        aug_gram << "(assert (= INT_CONSTS ";
        aug_gram << "(Int_either_" << lf.getConsts().size() << " ";
        for (auto& c : lf.getConsts())
        {
          aug_gram << c << " ";
        }
        aug_gram << ")))" << endl;

        // Read in entire user grammar
        ifstream infile(gram_file);
        aug_gram << infile.rdbuf();

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
    }

    Expr getAllLemmas()
    {
      return conjoin(learnedExprs, m_efac);
    }

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

      all_vars[bind::typeOf(var)].push_back(var);
      added = true;

      return added;
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

    Expr getRandCand(Expr root)
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
          // Randomly select from the available productions.
          // Offset by 1 because arg(0) is the fdecl.
          int randindex = (rand() % (root->arity() - 1)) + 1;

          return getRandCand(root->arg(randindex));
        }
        else
        {
          // Root is user-defined non-terminal or function
          if (defs[root] != NULL)
            // Root is user-defined non-terminal
            return getRandCand(defs[root]);

          // Else, root is user-defined function without eithers
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        return root;
      }

      // Root is Z3-defined non-terminal or user-defined function (w/o eithers)

      ExprVector expanded_args;

      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
      {
        expanded_args.push_back(getRandCand(*itr));
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
          randcand = simplifyBool(simplifyArithm(getRandCand(inv), false, false));
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
