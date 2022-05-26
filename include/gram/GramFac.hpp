#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"
#include "deep/Distribution.hpp"

#include <fstream>
#include <cctype>
#include <regex>
#include <tuple>
#include <random>

typedef unordered_set<ufo::Expr> ExprUSet;
typedef unordered_map<ufo::Expr, ufo::Expr> ExprUMap;

#include "gram/ParseTree.hpp"
#include "gram/TravPos.hpp"
#include "gram/PairHash.hpp"
#include "gram/TravParams.hpp"
#include "gram/CFGUtils.h"
#include "gram/Constraint.h"
#include "gram/Grammar.h"
#include "gram/Constraint.hpp"
#include "gram/Traversal.hpp"
#include "gram/RndTrav.hpp"
#include "gram/CoroTrav.hpp"
#include "gram/NewTrav.hpp"

#include "gram/CFGUtils.hpp"
#include "gram/Grammar.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // The maximum number of previous candidates we store.
  const int MAXGRAMCANDS = 100;

  class GRAMfactory
  {
    private:

    ExprFactory &m_efac;

    EZ3 &z3;

    // Previously generated candidates from sample grammar
    ExprUSet gramCands;
    deque<Expr> gramCandsOrder;

    // Variables for debugging coroutine creation/deletion
    //unordered_map<Expr, int> currnumtravcoros;
    //int currnumcandcoros = 0;

    // Key: <Non-terminal, Production>
    // Value: number of candidates generated with NT->Prod expansion
    unordered_map<std::pair<Expr,Expr>,mpz_class> candnum;

    // Total number of candidates we've generated (not necessarily returned)
    mpz_class totalcandnum = 0;

    // The grammar being used
    Grammar gram;

    Traversal *traversal = NULL;
    TravParams params;

    // Stored for later
    VarMap vars, othervars;
    ConstMap consts;

    // Whether to print debugging information or not.
    int printLog;

    public:

    bool initialized = false;
    bool done = false;

    private:

    bool shoulddefer(Grammar& gram, const Expr& nt, const Expr& expand)
    {
      //outs() << "shoulddefer(" << nt << ", " << expand << ") = ";
      //outs().flush();
      auto prod = make_pair(nt, expand);
      bool ret;
      if (gram.priomap.at(nt).at(expand) >= 1 || candnum[prod] == 0)
        ret = false;
      else
        ret = candnum[prod] > gram.priomap.at(nt).at(expand)*totalcandnum;
      //outs() << ret << "\n";
      return ret;
    }

    bool ptshoulddefer(const ParseTree &pt)
    {
      bool ret = false;
      pt.foreachPt([&] (const Expr &nt, const ParseTree &expand)
      {
        ret |= shoulddefer(gram, nt, expand.data());
      });
      return ret;
    }

    template<typename T>
    void printvec(std::ostream &os, T vec)
    {
      os << "[";
      for (auto &t : vec)
      {
        os << " " << t;
      }
      os << " ]";
    }

    void initTraversal()
    {
      if (traversal)
        delete traversal;
      switch (params.method)
      {
        case TPMethod::RND:
          traversal = new RndTrav(gram, params);
          break;
        case TPMethod::CORO:
          traversal = new CoroTrav(gram, params);
          break;
        case TPMethod::NEWTRAV:
          traversal = new NewTrav(gram, params,
            [&] (const Expr& ei, const Expr& exp)
            { return shoulddefer(gram, ei, exp); });
          break;
        case TPMethod::NONE:
          errs() << "WARNING: Traversal method set to NONE. Segfaults inbound!" << endl;
          break;
      }
    }

    public:

    // Whether or not to print candidates before simplification. For debug.
    bool b4simpl;

    GRAMfactory(ExprFactory &_efac, EZ3 &_z3, int _printLog) :
      m_efac(_efac), z3(_z3), printLog(_printLog) {}

    /*void addVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
    }*/

    void addOtherVar(Expr var)
    {
      othervars[bind::typeOf(var)].insert(var);
    }

    void addIntConst(cpp_int iconst)
    {
      consts[mk<INT_TY>(m_efac)].insert(mkMPZ(iconst, m_efac));
    }

    void addIncVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::INC));
    }

    void addDecVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::DEC));
    }

    void addConstVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::CONST));
    }

    void addUnknownVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::CONST));
    }

    void setParams(TravParams _params)
    {
      bool needInitTrav = initialized && params.method != _params.method;
      params = _params;
      if (needInitTrav)
      {
        // Wrap in assert so only printed in debug builds.
        assert(errs() << "WARNING: Re-initializing traversal. Make sure this is what you want!" << endl);
        initTraversal();
      }
    }

    TravParams getParams()
    {
      return params;
    }

    // Parse the grammar file. Must be called after addVar(s).
    void initialize(string gram_file, string inv_fname, bool _b4simpl)
    {
      b4simpl = _b4simpl;
      if (gram_file.empty())
        return;
      gram = std::move(CFGUtils::parseGramFile(gram_file, inv_fname, z3,
          m_efac, printLog, vars, othervars));
      initialized = true;
    }

    void extract_consts(const CHCs& chcs)
    {
      ExprUSet nums;
      for (const auto &chc : chcs.chcs)
        filter(chc.body, bind::isNum, inserter(nums, nums.begin()));
      if (printLog) outs() << "extract_consts found: ";
      for (const auto& num : nums)
      {
        if (printLog) outs() << num << " (type " << typeOf(num) << ") ";
        consts[typeOf(num)].insert(num);
        if (bind::isNum(num))
        {
          Expr neg = NULL;
          if (isOpX<MPZ>(num))
          {
            // To help the C++ template deduction.
            mpz_class negmpz = -getTerm<mpz_class>(num);
            neg = mkTerm(negmpz, num->efac());
          }
          else if (isOpX<MPQ>(num))
          {
            mpq_class negmpq = -getTerm<mpq_class>(num);
            neg = mkTerm(negmpq, num->efac());
          }
          else if (is_bvnum(num))
          {
            mpz_class negmpz = -bv::toMpz(num);
            neg = bv::bvnum(negmpz, bv::width(num->right()), num->efac());
          }

          if (neg)
          {
            if (printLog) outs() << neg << " (type " << typeOf(neg) << ") ";
            consts[typeOf(num)].insert(neg);
          }
        }
      }
      if (printLog) outs() << endl;
    }

    // Properly initialize *_CONSTS now that we've found them
    void initialize_consts()
    {
      for (const auto &sort_consts : consts)
        for (Expr c : sort_consts.second)
          gram.addConst(c);

      if (initialized)
      {
        initTraversal();
      }
    }

    void printSygusGram()
    {
      outs() << CFGUtils::toSyGuS(gram, z3);
    }

    std::list<ParseTree> deferred_cands;
    bool ignoreprios = false;
    ParseTree getCandidate_Done()
    {
      if (deferred_cands.size() != 0)
      {
        if ((printLog || b4simpl) && !ignoreprios)
        {
          outs()<< "Done with normal candidates, using deferred ones" << endl;
        }
        if (!ignoreprios)
          ignoreprios = true;
        ParseTree ret = deferred_cands.front();
        deferred_cands.pop_front();
        return ret;
      }

      outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
      done = true;
      //exit(0);
      return NULL;

    }

    Expr getFreshCandidate()
    {
      if (gram.root == NULL)
        return NULL; // Should never happen, but handle just in case

      Expr nextcand = NULL;
      ParseTree nextpt = NULL;

      /*for (auto& kv : currnumtravcoros)
        outs() << "currnumtravcoros[" << kv.first << "] = " << kv.second << "\n";
      outs() << "currnumcandcoros = " << currnumcandcoros << "\n";*/

      // Generate a new candidate from the grammar, and simplify
      while (!nextcand)
      {
        if (!traversal->IsDone())
          nextpt = traversal->Increment();
        else
        {
          nextpt = getCandidate_Done();
          if (!nextpt) return NULL;
        }
        if (!nextpt) continue;
        nextcand = nextpt;

        // Update candnum and totalcandnum
        nextpt.foreachPt([&] (const Expr& nt, const ParseTree& prod)
          {
            candnum[make_pair(nt, prod.data())]++;
          });
        totalcandnum++;

        if (b4simpl)
          outs() << "Before simplification: " << nextcand << endl;

        if (!gram.satsConstraints(nextpt))
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Doesn't satisfy constraints" << endl;
          continue;
        }

        nextcand = simplifyBool(simplifyArithm(nextcand));
        if (isOpX<TRUE>(nextcand) || isOpX<FALSE>(nextcand))
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Tautology/Contradiction" << endl;
          continue;
        }

        if (!ignoreprios && ptshoulddefer(nextpt))
        {
          deferred_cands.push_back(nextpt);
          nextpt = NULL;
          nextcand = NULL;
          if (b4simpl)
            outs() << "Need to defer candidate" << endl;
          continue;
        }

        if (!gramCands.insert(nextcand).second)
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Old candidate" << endl;
          continue;
        }

        if (gramCandsOrder.size() == MAXGRAMCANDS)
        {
          gramCands.erase(gramCandsOrder[0]);
          gramCandsOrder.pop_front();
        }
        gramCandsOrder.push_back(nextcand);
        break;
      }

      return nextcand;
    }
  };
}

#endif
