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
    unordered_map<std::pair<Expr,Expr>,int> candnum;

    // Total number of candidates we've generated (not necessarily returned)
    int totalcandnum = 0;

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

    bool shoulddefer(Grammar& gram, const Expr& either, const Expr& expand)
    {
      auto prod = make_pair(either, expand);
      if (gram.priomapat(prod) >= 1 || candnum[prod] == 0)
        return false;
      return candnum[prod] > (int)(gram.priomapat(prod)*totalcandnum);
    }

    bool ptshoulddefer(const ParseTree &pt)
    {
      bool ret = false;
      pt.foreachExpansion([&] (const Expr &nt, const Expr &expand)
      {
        ret |= shoulddefer(gram, gram.defs.at(nt), expand);
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
      consts[mk<INT_TY>(m_efac)].push_back(mkMPZ(iconst, m_efac));
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
      gram = CFGUtils::parseGramFile(gram_file, inv_fname, z3,
          m_efac, printLog, vars, othervars);
      initialized = true;
    }

    // Properly initialize INT_CONSTS now that we've found them
    void initialize_intconsts()
    {
      auto &intconsts = consts[mk<INT_TY>(m_efac)];
      if (intconsts.size() != 0)
      {
        Expr eitherfunc = bind::fdecl(mkTerm(string("either"), m_efac),
            ExprVector(intconsts.size(), m_efac.mkTerm(INT_TY())));

        Expr int_consts_decl = bind::intConst(mkTerm(string(INT_CONSTS), m_efac));
        gram.defs[int_consts_decl] = bind::fapp(eitherfunc, intconsts);
      }

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
        nextpt.foreachExpansion([&] (const Expr& nt, const Expr& prod)
          {
            candnum[make_pair(gram.defs.at(nt), prod)]++;
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
