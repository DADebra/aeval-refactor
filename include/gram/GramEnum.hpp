#ifndef __GRAMENUM__HPP__
#define __GRAMENUM__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include <set>
#include <unordered_map>
#include <list>

#include "gram/PairHash.hpp"

namespace ufo
{

class GramEnum
{
  // The maximum number of previous candidates we store.
  const int MAXGRAMCANDS = 200;

  // Previously generated candidates from sample grammar
  ExprUSet gramCands;
  deque<Expr> gramCandsOrder;

  // Key: <Non-terminal, Production>
  // Value: number of candidates generated with NT->Prod expansion
  unordered_map<std::pair<Expr,Expr>,mpz_class> candnum;
  // Total number of candidates we've generated (not necessarily returned)
  mpz_class totalcandnum = 0;

  std::list<ParseTree> deferred_cands;
  bool ignoreprios = false;

  // The grammar being used
  Grammar& gram;

  Traversal *traversal = NULL;
  TravParams params;

  ParseTree lastpt;
  Expr lastexpr;

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

  void gramReset()
  {
    travReset();
    gramCands.clear();
    gramCandsOrder.clear();
  }

  void travReset()
  {
    totalcandnum = 0;
    candnum.clear();
    deferred_cands.clear();
    ignoreprios = false;
    lastpt = NULL;
    lastexpr = NULL;
  }

  void initTraversal()
  {
    if (traversal)
    {
      delete traversal;
      traversal = NULL;
      travReset();
    }
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

  ParseTree getCandidate_Done()
  {
    if (deferred_cands.size() != 0)
    {
      if (debug && !ignoreprios)
      {
        outs() << "Done with normal candidates, using deferred ones" << endl;
      }
      if (!ignoreprios)
        ignoreprios = true;
      ParseTree ret = deferred_cands.front();
      deferred_cands.pop_front();
      return ret;
    }

    //exit(0);
    return NULL;

  }

  public:

  int debug;
  bool b4simpl = false;

  bool simplify;

  GramEnum(Grammar& _gram, const TravParams* _params = NULL, bool _simplify = false, int _debug = 0) :
    gram(_gram), simplify(_simplify), debug(_debug)
  {
    if (_params)
      SetParams(*_params);
  }
  ~GramEnum()
  {
    if (traversal)
    {
      delete traversal;
      traversal = NULL;
    }
  }

  void SetGrammar(Grammar& _gram)
  {
    gram = _gram;
    gramReset();
    Restart();
  }

  void Restart()
  {
    if (params.method != TPMethod::NONE)
      initTraversal();
  }

  const Grammar& GetGrammar() const { return gram; }

  void SetParams(TravParams _params)
  {
    bool needInitTrav = params != _params;
    TPMethod oldmeth = params.method;
    params = _params;
    if (params.iterdeepen && !gram.isInfinite())
    {
      if (debug > 2)
        outs() << "NOTE: Finite grammar but iterative deepening enabled. Disabling iterative deepening (as it does nothing here)" << endl;
      params.iterdeepen = false;
    }
    if (params.maxrecdepth != -2 && !gram.isInfinite())
    {
      params.maxrecdepth = 0;
      if (debug > 2)
        outs() << "NOTE: Finite grammar but maxrecdepth > 0. Setting maxrecdepth = 0 (as it does nothing here)" << endl;
    }
    if (needInitTrav)
    {
      if (oldmeth != TPMethod::NONE && traversal && !traversal->IsDone())
        // Wrap in assert so only printed in debug builds.
        assert(errs() << "WARNING: Re-initializing traversal. Make sure this is what you want!" << endl);
      initTraversal();
    }
  }

  TravParams GetParams() const
  {
    return params;
  }

  bool IsDone() const
  {
    if (!traversal)
      return true;
    if (!traversal->IsDone())
      return false;
    return deferred_cands.size() == 0;
  }

  int GetCurrDepth() const
  {
    if (!traversal)
      return -1;
    return traversal->GetCurrDepth();
  }

  const ExprUSet& GetCurrUniqueVars() const
  { return traversal->GetCurrUniqueVars(); }

  Expr Increment()
  {
    Expr nextcand = NULL;
    ParseTree nextpt = NULL;

    // Generate a new candidate from the grammar, and simplify
    while (!nextcand)
    {
      if (traversal->IsDone() && deferred_cands.size() == 0)
        return NULL;
      if (!traversal->IsDepthDone() || deferred_cands.size() == 0)
      {
        nextpt = traversal->Increment();
        if (debug && traversal->IsDepthDone())
          outs() << "Done with depth " << traversal->GetCurrDepth() << endl;
      }
      else
      {
        nextpt = getCandidate_Done();
        if (!nextpt && traversal->IsDone()) return NULL;
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

      if (simplify)
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

    lastpt = nextpt;
    lastexpr = nextcand;

    return nextcand;
  }

  // Simplified (if enabled)
  Expr GetCurrCand() const { return lastexpr; }

  // Unsimplified
  ParseTree GetCurrPT() const { return lastpt; }
};

}

#endif
