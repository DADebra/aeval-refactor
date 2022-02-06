#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"
#include "deep/Distribution.hpp"

#include <fstream>
#include <cctype>
#include <regex>
#include <tuple>
#include <random>

#include <boost/coroutine2/coroutine.hpp>
#include <boost/optional.hpp>
#include <boost/optional/optional_io.hpp>

#include "ParseTree.hpp"
#include "TravPos.hpp"
#include "PairHash.hpp"

using namespace std;
using namespace boost;
using namespace boost::coroutines2;

namespace ufo
{
  const char* ANY_INV = "ANY_INV";
  const char* INT_CONSTS = "INT_CONSTS";
  // The maximum number of previous candidates we store.
  const int MAXGRAMCANDS = 100;
  // The maximum arity of 'either' functions we write.
  const int NUMEITHERS = 100;

  typedef unordered_set<Expr> ExprUSet;
  typedef unordered_map<Expr, Expr> ExprUMap;

  // Candidate generation method.
  //   RND - Completely random candidate without replacement.
  //   TRAV - Traverse full grammar up to specified depth.
  //   NEWTRAV - Coroutine-less TRAV.
  enum class GramGenMethod { RND, TRAV, NEWTRAV };

  enum class TravParamDirection { LTR, RTL, RND };
  enum class TravParamOrder { FORWARD, REVERSE, RND };
  enum class TravParamType { ORDERED, STRIPED };
  enum class TravParamPrio { SFS, DFS, BFS };

  // Parameters for generation using grammar.
  //   1st - GramGenMethod
  //   2nd - Maximum recursion depth
  typedef std::tuple<GramGenMethod, int, TravParamDirection, TravParamOrder,
          TravParamType, TravParamPrio, bool, unsigned> GramParams;

  class GRAMfactory
  {
    private:

    // A coroutine returning an Expr.
    typedef coroutine<Expr>::pull_type ExprCoro;

    // A coroutine returning a ParseTree.
    typedef coroutine<ParseTree>::pull_type PTCoro;

    class PTCoroCacheIter;

    class PTCoroCache
    {
      protected:
      vector<ParseTree> outcache;
      PTCoro coro;

      friend PTCoroCacheIter;

      public:
      PTCoroCache(PTCoro _coro) : coro(std::move(_coro)) {}

      PTCoroCacheIter begin()
      {
        return PTCoroCacheIter(0, *this);
      }

      PTCoroCacheIter end()
      {
        return PTCoroCacheIter(-1, *this);
      }
    };

    class PTCoroCacheIter
    {
      int pos = 0;
      PTCoroCache &cache;

      inline void advancecoro()
      {
        while (cache.outcache.size() <= pos && cache.coro)
        {
          cache.outcache.push_back(cache.coro.get());
          cache.coro();
        }
        if (cache.outcache.size() <= pos)
          pos = -1;
      }

      public:

      PTCoroCacheIter(int _pos, PTCoroCache& _cache) : pos(_pos),
        cache(_cache) {}

      operator bool()
      {
        return pos >= 0;
      }

      ParseTree get()
      {
        if (pos < 0)
          return nullptr;

        advancecoro();

        if (pos < 0)
          return nullptr;

        return cache.outcache[pos];
      }

      void operator()()
      {
        ++pos;
        advancecoro();
      }

      PTCoroCacheIter& operator++()
      {
        ++pos;
        advancecoro();
        return *this;
      }

      ParseTree operator*()
      {
        return get();
      }

      PTCoroCacheIter begin()
      {
        return std::move(PTCoroCacheIter(pos, cache));
      }

      PTCoroCacheIter end()
      {
        return std::move(PTCoroCacheIter(-1, cache));
      }
    };

    class tuplehash
    {
      public:
      size_t operator()(const std::tuple<Expr,int,std::shared_ptr<ExprUSet>,
      Expr>& tup) const
      {
        return std::hash<Expr>()(std::get<0>(tup)) *
          std::hash<int>()(std::get<1>(tup)) *
          std::hash<std::shared_ptr<ExprUSet>>()(std::get<2>(tup)) *
          std::hash<Expr>()(std::get<3>(tup));
      }
    };

    // The main coroutine we use to traverse the grammar.
    std::unique_ptr<PTCoro> getNextCandTrav;

    // Needed for candidate generation.
    ExprFactory &m_efac;

    // Needed for parsing grammar.
    EZ3 &z3;

    // Needed for evaluating constraints.
    ZSolver<EZ3> m_smt_solver;

    // Previously generated candidates from sample grammar
    ExprUSet gramCands;
    deque<Expr> gramCandsOrder;

    // Variables for debugging coroutine creation/deletion
    //unordered_map<Expr, int> currnumtravcoros;
    //int currnumcandcoros = 0;

    // The sub-candidates previously generated with root == key
    unordered_map<std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr>,
      PTCoroCache,tuplehash> ptcorocache;

    // Our current position in the CFG traversal
    TravPos rootpos;

    // Key: Non-terminal, Value: Productions in b/ieither# format
    ExprUMap defs;

    // List of FAPP (or EQ, GT, etc.) constraints specified in the grammar
    ExprVector constraints;

    // Key: <Non-terminal, Production>, Value: Priority
    unordered_map<std::pair<Expr, Expr>, cpp_rational> priomap;

    // priomap, but for getRandCand
    // Key: Non-terminal, Value: Distribution, in order given by CFG
    unordered_map<Expr, discrete_distribution<int>> distmap;

    // Needed for randomness in getRandCand
    default_random_engine randgenerator;

    // Key: <Non-terminal, Production>
    // Value: number of candidates generated with NT->Prod expansion
    unordered_map<std::pair<Expr,Expr>,int> candnum;

    // Total number of candidates we've generated (not necessarily returned)
    int totalcandnum = 0;

    // The root of the tree of the grammar
    Expr inv;

    struct varless
    {
      bool operator()(const Expr& l, const Expr& r) const
      {
        string lstr = lexical_cast<string>(fname(l)->left());
        string rstr = lexical_cast<string>(fname(r)->left());
        return lstr < rstr;
      }
    };
    typedef set<Expr,varless> varset;

    // All variables mentioned in the file, regardless of type.
    // Variables are for the invariant stored in 'inv'
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, varset> inv_vars;

    // Variables for the other invariants in the input file.
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, varset> other_inv_vars;

    // Set of integer constants that appear in the program.
    set<cpp_int> int_consts;

    // Map of <STRING,Expr> for e.g. `under` constraint.
    unordered_map<Expr,Expr> strcache;

    // Whether to print debugging information or not.
    bool printLog;

    /*** PARAMETERS (respective to GramParams) ***/

    // How this GRAMfactory will generate candidates.
    GramGenMethod genmethod;

    // The maximum recursion depth during traversal.
    int maxrecdepth;

    TravParamDirection travdir;
    TravParamOrder travorder;
    TravParamType travtype;
    TravParamPrio travprio;

    // Whether or not to print candidates before simplification. For debug.
    bool b4simpl;

    // The timeout for the SMT solver runs, if any occur.
    unsigned timeout;

    public:

    bool initialized = false;
    bool done = false;

    private:

    // exp is e.g. (= iterm iterm), nonterm is e.g. iterm
    bool isRecursive(const Expr& exp, const Expr& nonterm)
    {
      for (auto itr = exp->args_begin(); itr != exp->args_end(); ++itr)
      {
        if (isRecursive(*itr, nonterm))
          return true;
      }
      // Handle simple recursion
      if (exp == nonterm)
        return true;

      return false;
    }

    Expr collapsePT(const ParseTree& pt)
    {
      if (pt.children().size() == 0)
        return pt.data();
      else if (pt.children().size() == 1)
      {
        if (!isOpX<FAPP>(pt.data()))
          return m_efac.mkUnary(pt.data()->op(), collapsePT(pt.children()[0]));
        return collapsePT(pt.children()[0]);
      }
      else
      {
        ExprVector eargs;
        for (ParseTree subpt : pt.children())
        {
          eargs.push_back(collapsePT(subpt));
        }
        return m_efac.mkNary(pt.data()->op(), eargs);
      }
    }

    inline void foreachPt(const ParseTree& pt,
      const function<void(const Expr&, const ParseTree&)>& func)
    {
      if (pt.children().size() == 0)
        return;
      else if (pt.children().size() == 1)
      {
        const ParseTree* realnt = &pt;
        while (defs.count(realnt->children()[0].data()) != 0)
          realnt = &realnt->children()[0];

        func(pt.data(), realnt->children()[0]);

        return foreachPt(pt.children()[0], func);
      }
      else
      {
        for (auto &subpt : pt.children())
          foreachPt(subpt, func);
      }
    }

    inline void foreachExp(const ParseTree& pt,
      const function<void(const Expr&, const Expr&)>& func)
    {
      return foreachPt(pt, [&] (const Expr& nt, const ParseTree& prod)
      {
        func(nt, prod.data());
      });
    }

    // A map of <Non-terminal, Set of Expansions> (see findExpansions)
    typedef unordered_map<Expr,unordered_set<ParseTree>> ExpansionsMap;

    // Key: Non-terminal   Value: Set of Expr's that First expands to
    void findExpansions(const ParseTree& pt, ExpansionsMap& outmap)
    {
      return foreachPt(pt, [&] (const Expr& nt, const ParseTree& prod)
      {
        outmap[nt].insert(prod);
      });
    }

    // Returns the ParseTree (node) whose `data` field matches the given `data`
    //   argument and is a parent of `child`.
    // When two parents have the same `data` argument, picks the one
    //   closest to the root.
    // Returns NULL when no parent found.
    ParseTree findHighestParent(Expr data, const ParseTree& child)
    {
      if (!child)
        return NULL;
      if (child.data() == data)
      {
        ParseTree nextparent = std::move(
          findHighestParent(data, child.parent()));
        if (nextparent)
          return nextparent; // We found a higher parent
        return child;
      }
      if (!child.parent())
        return NULL; // Couldn't find parent with given data
      return std::move(findHighestParent(data, child.parent()));
    }

    inline Expr stoe(Expr e)
    {
      assert(isOpX<STRING>(e));
      assert(strcache.count(e) != 0);
      return strcache.at(e);
    }

    typedef unordered_map<Expr,ParseTree> PtExpMap;
    void foreachExpans(Expr con, const ExpansionsMap& expmap,
      function<bool(const PtExpMap&)> func)
    {
      ExprVector fapps(expmap.size());
      filter(con, [] (Expr e) {
        return isOpX<FAPP>(e) && e->arity() == 1; }, fapps.begin());
      // Note that because of the internal ExprSet that dagVisit uses,
      //   we don't need to purge duplicates from `fapps`.
      ExprVector from;
      for (auto &f : fapps)
        if (f && expmap.count(f) != 0) from.push_back(f);
      vector<ParseTree> to(from.size());
      auto makemap = [&] () -> PtExpMap
      {
        PtExpMap ret;
        for (int i = 0; i < from.size(); ++i)
          assert(ret.emplace(from[i], to[i]).second);
        return std::move(ret);
      };

      if (from.size() == 0)
      {
        // If there are no expansions, we still need to evaluate the constraint
        func(makemap());
        return;
      }

      function<bool(int)> perm = [&] (int pos)
      {
        if (pos == from.size())
        {
          if (!func(makemap()))
            return false;
        }
        else
          for (auto &expand : expmap.at(from[pos]))
          {
            to[pos] = expand;
            if (!perm(pos + 1))
              return false;
          }
        return true;
      };
      perm(0);
    }

    typedef unordered_map<pair<Expr,ParseTree>,ExprUSet> seen_type;
    optional<cpp_int> evaluateArithExpr(Expr arith, const PtExpMap& expmap,
      seen_type& se)
    {
      auto aritharg = [&] (int i) -> Expr
      {
        if (expmap.count(arith->arg(i)) != 0)
          return expmap.at(arith->arg(i)).data();
        else
          return arith->arg(i);
      };
      if (isOpX<FAPP>(arith))
      {
        if (expmap.count(arith) != 0)
          return evaluateArithExpr(expmap.at(arith).data(), expmap, se);
        else
          return none;
      }

      if (isOpX<ITE>(arith))
      {
        tribool res = evaluateCmpExpr(aritharg(0), expmap, se);
        if (indeterminate(res))
          return none;
        if (res)
          return evaluateArithExpr(aritharg(1), expmap, se);
        else
          return evaluateArithExpr(aritharg(2), expmap, se);
      }

      if (isOpX<MPZ>(arith))   return lexical_cast<cpp_int>(arith);
      if (arith->arity() != 2) return none;

      optional<cpp_int> lhs = evaluateArithExpr(aritharg(0), expmap, se);
      if (!lhs) return none;
      cpp_int ilhs = *lhs;

      if (isOpX<UN_MINUS>(arith)) return optional<cpp_int>(-ilhs);
      if (isOpX<ABS>(arith))   return ilhs > 0 ? ilhs : -ilhs;

      optional<cpp_int> rhs = evaluateArithExpr(aritharg(1), expmap, se);
      if (!rhs) return none;
      cpp_int irhs = *rhs;

      if (isOpX<PLUS>(arith))  return optional<cpp_int>(ilhs + irhs);
      if (isOpX<MINUS>(arith)) return optional<cpp_int>(ilhs - irhs);
      if (isOpX<MULT>(arith))  return optional<cpp_int>(ilhs * irhs);
      if (isOpX<DIV>(arith) || isOpX<IDIV>(arith))
        return optional<cpp_int>(ilhs / irhs);
      if (isOpX<MOD>(arith))
      {
        // Copied from include/ae/ExprSimpl.hpp
        if (irhs < 0)
          irhs = -irhs;
        if (ilhs < 0)
          ilhs += ((-ilhs / irhs) + 1) * irhs;
        ilhs = ilhs % irhs;
        return ilhs;
      }
      return none;
    }

    tribool evaluateCmpExpr(Expr cmp, const PtExpMap& expmap,
      seen_type& seenexpans)
    {
      auto cmparg = [&] (int i) -> Expr
      {
        if (expmap.count(cmp->arg(i)) != 0)
          return expmap.at(cmp->arg(i)).data();
        else
          return cmp->arg(i);
      };

      string conn;
      if (isOpX<FAPP>(cmp))
        conn = lexical_cast<string>(bind::fname(cmp)->left());

      // simplifyArithm is also simplifying comparisons
      if (isOpX<FALSE>(cmp))
        return false;
      if (isOpX<TRUE>(cmp))
        return true;
      if (isOpX<NEG>(cmp))
        return !evaluateCmpExpr(cmp->left(), expmap, seenexpans);
      if (isOpX<EQ>(cmp) || (conn == "equal" && cmp->arity() > 2))
      {
        int si = conn == "equal" ? 1 : 0;
        optional<cpp_int> first = evaluateArithExpr(cmparg(si),
          expmap, seenexpans);
        if (!first && !isOpX<FAPP>(cmparg(si)) && !isOpX<MPZ>(cmparg(si)) &&
        !isOpX<MPQ>(cmparg(si)))
          return indeterminate;
        for (int i = si + 1; i < cmp->arity(); ++i)
        {
          if (first)
          {
            optional<cpp_int> inti = evaluateArithExpr(cmparg(i),
              expmap, seenexpans);
            if (!inti)
              return indeterminate;
            if (inti != first)
              return false;
          }
          else
          {
            if (!isOpX<FAPP>(cmparg(i)) && !isOpX<MPZ>(cmparg(i)) &&
            !isOpX<MPQ>(cmparg(i)))
              return indeterminate;
            if (cmparg(i) != cmparg(si))
              return false;
          }
        }
        return true;
      }
      if (isOpX<NEQ>(cmp) && cmp->arity() > 1)
      {
        for (int p1 = 0; p1 < cmp->arity(); ++p1)
        {
          optional<cpp_int> first = evaluateArithExpr(cmparg(p1),
            expmap, seenexpans);
          for (int p2 = p1 + 1; p2 < cmp->arity(); ++p2)
          {
            if (first)
            {
              optional<cpp_int> second = evaluateArithExpr(cmparg(0),
                expmap, seenexpans);
              if (!second)
                return indeterminate;
              if (*first == *second)
                return false;
            }
            if (!isOpX<FAPP>(cmparg(p1)) && !isOpX<MPZ>(cmparg(p1)) &&
            !isOpX<MPQ>(cmparg(p1)))
              return indeterminate;
            if (cmparg(p1) == cmparg(p2))
              return false;
          }
        }
        return true;
      }
      if (isOpX<AND>(cmp) || isOpX<OR>(cmp) || isOpX<XOR>(cmp))
      {
        bool doAnd = isOpX<AND>(cmp),
             doXor = isOpX<XOR>(cmp);
        tribool ret = evaluateCmpExpr(cmparg(0), expmap, seenexpans);
        for (int i = 1; i < cmp->arity(); ++i)
        {
          tribool subret = evaluateCmpExpr(cmparg(i), expmap, seenexpans);
          if (doXor)
            ret = (subret || ret) && !(subret && ret);
          else if (doAnd)
            ret = subret && ret;
          else
            ret = subret || ret;
        }
        return ret;
      }
      if (isOpX<IMPL>(cmp))
        return !evaluateCmpExpr(cmparg(0),expmap,seenexpans) ||
          evaluateCmpExpr(cmparg(1),expmap,seenexpans);
      if (isOpX<ITE>(cmp))
        return evaluateCmpExpr(cmparg(0),expmap,seenexpans) ?
          evaluateCmpExpr(cmparg(1),expmap,seenexpans) :
          evaluateCmpExpr(cmparg(2),expmap,seenexpans);
      if (isOpX<FAPP>(cmp) || isOpX<NEQ>(cmp))
      {
        if (conn == "equal" || isOpX<NEQ>(cmp))
        {
          Expr lhs;
          if (isOpX<NEQ>(cmp))
          {
            assert(cmp->arity() == 1);
            lhs = cmp->arg(0);
          }
          else
          {
            assert(cmp->arity() == 2);
            lhs = cmp->arg(1);
          }
          pair<Expr,ParseTree> key = make_pair(lhs, ParseTree(NULL));
          if (expmap.count(lhs) == 0)
            return true;

          bool firstinsert = seenexpans.count(key) == 0;
          bool res = seenexpans[key].insert(expmap.at(lhs).data()).second;
          return conn == "equal" ? firstinsert || !res : res;
        }
        else if (conn == "equal_under" || conn == "distinct_under")
        {
          if (cmp->arity() == 3)
          {
            assert(isOpX<FAPP>(cmp));
            Expr lhs = stoe(cmp->arg(1));
            Expr rhs = cmp->arg(2);

            // Self-equal/distinct
            if (expmap.count(rhs) == 0)
              return true;

            ParseTree rhsexp = expmap.at(rhs); // The Expr that RHS expands to

            ParseTree parent = findHighestParent(lhs, rhsexp);
            if (!parent)
              return true;
            pair<Expr,ParseTree> key = make_pair(rhs, parent);
            bool firstinsert = seenexpans.count(key) == 0;
            bool res = seenexpans[key].insert(rhsexp.data()).second;
            return conn == "equal_under" ? firstinsert || !res : res;
          }

          // Else, pairwise equal/distinct
          assert(cmp->arity() > 3);

          Expr lhs = stoe(cmp->arg(1));

          for (int p1 = 2; p1 < cmp->arity(); ++p1)
          {
            if (expmap.count(cmp->arg(p1)) == 0)
              continue;
            for (int p2 = p1 + 1; p2 < cmp->arity(); ++p2)
            {
              if (expmap.count(cmp->arg(p2)) == 0)
                continue;
              ParseTree exp1 = expmap.at(cmp->arg(p1));
              ParseTree par1 = findHighestParent(lhs, exp1);
              if (!par1)
                continue;
              ParseTree exp2 = expmap.at(cmp->arg(p2));
              ParseTree par2 = findHighestParent(lhs, exp2);
              if (!par2 || par1 != par2)
                continue;
              bool res;
              if (conn == "equal_under")
                res = exp1.data() == exp2.data();
              else
                res = exp1.data() != exp2.data();
              if (!res)
                return false;
            }
          }
          return true;
        }
        else if (conn == "expands")
        {
          Expr lhs = cmp->arg(1);
          Expr rhs = stoe(cmp->arg(2));
          if (expmap.count(lhs) == 0)
            return true;
          return expmap.at(lhs).data() == rhs;
        }
        else if (conn == "under")
        {
          Expr lhs = stoe(cmp->arg(1));
          Expr rhs = cmp->arg(2);
          if (expmap.count(rhs) == 0)
            return true;
          ParseTree parent = findHighestParent(lhs, expmap.at(rhs));

          return bool(parent);
        }
        else
          return indeterminate;
      }

      if (!isOp<ComparissonOp>(cmp))
        return indeterminate;
      if (cmp->arity() > 2)
        return indeterminate;

      optional<cpp_int> lo= evaluateArithExpr(cmp->arg(0),expmap,seenexpans),
                        ro= evaluateArithExpr(cmp->arg(1),expmap,seenexpans);
      if (!lo || !ro)
        return indeterminate;
      cpp_int li = *lo, ri = *ro;

      if (isOpX<LEQ>(cmp))
        return li <= ri;
      if (isOpX<GEQ>(cmp))
        return li >= ri;
      if (isOpX<LT>(cmp))
        return li < ri;
      if (isOpX<GT>(cmp))
        return li > ri;

      return indeterminate;
    }

    bool doesSatExpr(Expr con, const ExpansionsMap& expmap,
      bool doAny, Expr origcon)
    {
      bool needsolver = false;
      ExprVector assertexps;
      if (doAny)
        assertexps.push_back(mk<FALSE>(m_efac));
      else
        assertexps.push_back(mk<TRUE>(m_efac));

      //evalCmpExpr needs some shared state
      seen_type seenexpans;
      tribool ret = indeterminate;
      foreachExpans(con, expmap, [&] (const PtExpMap& exp)
      {
        tribool res = evaluateCmpExpr(con, exp, seenexpans);
        if (indeterminate(res))
        {
          // We (maybe) don't want Z3 to evaluate variables as
          //   non-determinate integers.
          RW<function<Expr(Expr)>> rw(new function<Expr(Expr)>(
            [&exp] (Expr e) -> Expr
          {
            if (isOpX<FAPP>(e) && exp.count(e) != 0)
              e = exp.at(e).data();
            if ((isOpX<EQ>(e) || isOpX<NEQ>(e)) &&
            all_of(e->args_begin(), e->args_end(), isOpX<FAPP,Expr>))
            {
              ExprVector args(e->arity());
              for (int i = 0; i < e->arity(); ++i)
                // Using memory location here as an easy way to get
                //   different symbolic variables to be
                //   a). predictable and b). unique
                args[i] = mkMPZ((unsigned long)e->arg(i), e->efac());
              return e->efac().mkNary(e->op(), args);
            }
            return e;
          }));
          Expr z3exp = dagVisit(rw, con);
          //m_smt_solver.assertExpr(exp);
          assertexps.push_back(z3exp);
          needsolver = true;
        }
        else if (!res && !doAny)
        {
          ret = false;
          return false;
        }
        else if (res && doAny)
        {
          ret = true;
          return false;
        }
        return true;
      });
      if (!indeterminate(ret))
        return bool(ret);

      if (needsolver)
      {
        m_smt_solver.reset();

        if (doAny)
          m_smt_solver.assertExpr(m_efac.mkNary(OR(), assertexps));
        else
          m_smt_solver.assertExpr(m_efac.mkNary(AND(), assertexps));

        static unordered_map<Expr,bool> didcomplain;
        if (!didcomplain[origcon])
        {
          outs() << "NOTE: Invoking SMT solver to evaluate constraint: " <<
            origcon->right() << "\n Freqhorn will go much slower!\n";
          didcomplain[origcon] = true;
        }
        tribool res = m_smt_solver.solve();
        if (indeterminate(res))
        {
          outs() << "ERROR: Indeterminate result in evaluating constraints:\n";
          m_smt_solver.toSmtLib(outs());
          outs() << endl;
          assert(0);
        }
        if (!res && !doAny)
          return false;
        else if (res && doAny)
          return true;
      }

      if (doAny)
        return false;
      else
        return true;
    }

    int calculateRecDepth(const ExpansionsMap& expmap, Expr nt)
    {
      if (expmap.count(nt) == 0)
        return 0;
      int depth = 0;
      for (const auto &pt : expmap.at(nt))
        if (isRecursive(pt.data(), nt))
          ++depth;
      return depth;
    }

    bool doesSatConstraints(const ParseTree& pt)
    {
      ExpansionsMap expmap;
      findExpansions(pt, expmap);

      for (auto &fullcon : constraints)
      {
        Expr con = fullcon->right();
        bool doAny = lexical_cast<string>(bind::fname(fullcon)->left()) ==
          "constraint_any";
        RW<function<Expr(Expr)>> fapprw(new function<Expr(Expr)>(
          [&expmap, &doAny, &pt, this] (Expr e) -> Expr
        {
          auto btoe = [&] (bool b) -> Expr
          {
            return b ? mk<TRUE>(e->efac()) : mk<FALSE>(e->efac());
          };

          if (isOpX<FAPP>(e))
          {
            string conname = lexical_cast<string>(bind::fname(e)->left());
            if (conname == "present")
            {
              Expr lhs = stoe(e->arg(1));
              // Could be evaluated in evaluateCmpExpr, but I want to keep
              //   the framework of global expression evaluation here.
              function<bool(const ParseTree&)> existhelper =
                [&] (const ParseTree& root) -> bool
              {
                if (root.data() == lhs)
                  return true;
                for (auto& child : root.children())
                  if (existhelper(child))
                    return true;
                return false;
              };
              return btoe(existhelper(pt));
            }
            else if (conname == "maxrecdepth")
            {
              Expr lhs = stoe(e->arg(1));
              if (expmap.count(lhs) == 0)
                return mkMPZ(cpp_int(0), e->efac());
              int deepest = 0;
              for (const auto &pt : expmap.at(lhs))
              {
                int depth = calculateRecDepth(expmap, lhs);
                if (depth > deepest)
                  deepest = std::move(depth);
              }
              return mkMPZ(cpp_int(deepest), e->efac());
            }
            else
              return e;
          }
          /*else if (isOpX<NEG>(e) && isOpX<NEQ>(e->left()) &&
            e->left()->arity() == 1)
          {
            // Shared between all objects; OK
            static unordered_map<Expr,Expr> eqapp;
            // Doesn't matter if index by e or e->left()
            if (eqapp.count(e->left()) != 0)
              return eqapp.at(e->left());
            Expr eqdecl = bind::fdecl(
              mkTerm(string("equal"), m_efac),
              ExprVector{ bind::typeOf(e->left()->left()) });
            eqapp.emplace(e->left(),
              bind::fapp(eqdecl, e->left()->left(), Expr()));
            return eqapp.at(e->left());
          }
          else if (isOpX<NEG>(e) && isOpX<FAPP>(e->left()))
          {
            Expr nfdecl = e->left()->left();
            string nfname = lexical_cast<string>(nfdecl->left());
            if (nfname == "under" || nfname == "not_under")
            {
              string opposite = nfname == "not_under" ? "under" : "not_under";
              // Shared between all objects; OK
              static unordered_map<Expr,Expr> notuapp;
              // Doesn't matter if index by e or e->left()
              if (notuapp.count(e->left()) != 0)
                return notuapp.at(e->left());
              Expr notudecl = bind::fdecl(
                mkTerm(string(opposite), m_efac),
                ExprVector{ nfdecl->arg(1), nfdecl->arg(2) });
              assert(e->left()->arity() == 3);
              notuapp.emplace(e->left(), bind::reapp(e->left(), notudecl));
              return notuapp.at(e->left());
            }
            else if (nfname == "equal")
            {
              return mk<NEQ>(e->left()->right());
            }
            else
              return e;
          }*/
          else
            return e;
        }));
        con = dagVisit(fapprw, con);
        if (!doesSatExpr(con, expmap, doAny, fullcon))
          return false;
      }

      return true;
    }

    inline bool shoulddefer(const Expr& nt, const Expr& expand)
    {
      auto prod = make_pair(nt, expand);
      if (priomap.count(prod) == 0)
        priomap.emplace(prod, 1);
      if (priomap[prod] >= 1 || candnum[prod] == 0)
        return false;
      return candnum[prod] > (int)(priomap[prod]*totalcandnum);
    }

    inline bool ptshoulddefer(const ParseTree &pt)
    {
      bool ret = false;
      foreachExp(pt, [&] (const Expr &nt, const Expr &expand)
      {
        ret |= shoulddefer(nt, expand);
      });
      return ret;
    }

    ParseTree gettrav(const Expr& root, const TravPos& travpos,
      std::shared_ptr<ExprUSet> qvars, Expr currnt, bool& needdefer)
    {
      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const varset& sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable
          return ParseTree(root);
        }
        else if (fname == "either")
        {
          needdefer= needdefer || shoulddefer(currnt, root->arg(travpos.pos));
          return gettrav(root->arg(travpos.pos),
            travpos.childat(travpos.pos), qvars, currnt, needdefer);
        }
        else if (defs.count(root) != 0)
        {
          // Root is non-terminal; expand
          return ParseTree(root, vector<ParseTree>{gettrav(defs.at(root),
            travpos, qvars, root, needdefer)});
        }
        else if (qvars != NULL && qvars->find(root->left()) != qvars->end())
        {
          // Root is a closed (quantified) variable
          return ParseTree(root);
        }
        else
        {
          // Should never happen
          // There's no definition, we're expanding an empty *_VARS
          outs() << "ERROR: There is no definition for user-defined " <<
            "non-terminal " << root << " in the CFG for " << inv <<
            ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
          assert(0);
          return NULL;
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal
        return ParseTree(root);
      }
      else
      {
        // Root is a Z3 function (e.g. (and ...))
        std::shared_ptr<ExprUSet> localqvars(new ExprUSet());

        if (qvars != NULL)
          for (auto& var : *qvars)
            localqvars->insert(var);

        if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
        {
          // Add quantifier variables to qvars
          for (int i = 0; i < root->arity() - 1; ++i)
          {
            localqvars->insert(root->arg(i));
          }
        }

        assert(travpos.childrensize() == root->arity());
        vector<ParseTree> newexpr(root->arity());

        // To reverse ('rtl'), we just invert newexpr and root->arg(i)
        function<ParseTree&(int)> newexprat;
        function<Expr(int)> rootarg;
        if (travdir == TravParamDirection::LTR)
        {
          newexprat = [&] (int i) -> ParseTree& { return newexpr[i]; };
          rootarg = [&] (int i) { return root->arg(i); };
        }
        else if (travdir == TravParamDirection::RTL)
        {
          newexprat = [&] (int i) -> ParseTree&
            { return newexpr[root->arity()-1-i]; };
          rootarg = [&] (int i) { return root->arg(root->arity()-1-i); };
        }

        if (travpos.inqueue() && travpos.pos.limit != -1)
        {
          return gettrav(root, travpos.queueat(travpos.pos),
            localqvars, currnt, needdefer);
        }

        for (int i = 0; i < travpos.childrensize(); ++i)
        {
          newexprat(i) = gettrav(rootarg(i), travpos.childat(i),
            localqvars, currnt, needdefer);
        }

        return ParseTree(root, std::move(newexpr));
      }
    }

    ParseTree newtrav(const Expr& root, TravPos& travpos,
      int currdepth = 0, std::shared_ptr<ExprUSet> qvars = NULL,
      Expr currnt = NULL)
    {
      assert(("Cannot increment TravPos which is done!", !travpos.isdone()));

      // Some operations should not cause copy-up; use constpos for these.
      const TravPos &constpos = travpos;

      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const varset& sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable
          travpos = TravPos(0, 1);
          ++travpos.pos;
          travpos.makedone();
          return ParseTree(root);
        }
        else if (fname == "either")
        {
          if (travpos.pos < 0)
          {
            // First-time initialize
            travpos = TravPos(1, root->arity());
            if (travtype != TravParamType::STRIPED)
            {
              if (travorder == TravParamOrder::FORWARD)
                ++travpos.pos;
              else if (travorder == TravParamOrder::REVERSE)
                --travpos.pos;
            }
          }

          if (travtype == TravParamType::STRIPED)
          {
            if (travorder == TravParamOrder::FORWARD)
              ++travpos.pos;
            else if (travorder == TravParamOrder::REVERSE)
              --travpos.pos;
          }

          // We're just checking, use const version of queueat()
          CircularInt checkpos = constpos.pos;

          int startpos = checkpos;
          while (constpos.childat(checkpos).isdone() ||
          (isRecursive(root->arg(checkpos), currnt) &&
           currdepth == maxrecdepth))
          {
            if (travorder == TravParamOrder::FORWARD)
              ++checkpos;
            else if (travorder == TravParamOrder::REVERSE)
              --checkpos;

            assert(checkpos != startpos);
          }

          startpos = checkpos;
          while (constpos.childat(checkpos).isdone() ||
           shoulddefer(currnt, root->arg(checkpos)) ||
           (isRecursive(root->arg(checkpos), currnt) &&
           currdepth == maxrecdepth))
          {
            if (travorder == TravParamOrder::FORWARD)
              ++checkpos;
            else if (travorder == TravParamOrder::REVERSE)
              --checkpos;

            if (checkpos == startpos)
            {
              if (isRecursive(root->arg(checkpos), currnt) &&
                currdepth == maxrecdepth)
              {
                travpos.makedone();
                // Purposeful return NULL, since this n.t. at this depth
                //   is empty.
                return NULL;
              }
              // All productions must be deferred; pick first one
              checkpos = startpos;
              break;
            }
          }

          travpos.pos = checkpos;

          ParseTree ret(NULL);
          int newdepth;
          if (isRecursive(root->arg(travpos.pos), currnt))
            newdepth = currdepth + 1;
          else
            newdepth = currdepth;

          assert(newdepth <= maxrecdepth);

          ret = newtrav(root->arg(travpos.pos),
            travpos.childat(travpos.pos), newdepth, qvars, currnt);

          // Check to see if we're done.
          checkpos = travpos.pos;
          while (travpos.childat(checkpos).isdone() ||
          (isRecursive(root->arg(checkpos), currnt) &&
           currdepth == maxrecdepth))
          {
            if (travorder == TravParamOrder::FORWARD)
              ++checkpos;
            else if (travorder == TravParamOrder::REVERSE)
              --checkpos;

            if (checkpos == travpos.pos)
            {
              // We're done with this either; move 'pos' past end.
              travpos.makedone();
              break;
            }
          }

          assert(ret);

          return ret;
        }
        else if (defs.count(root) != 0)
        {
          // Root is non-terminal; expand
          return ParseTree(root, vector<ParseTree>{newtrav(defs.at(root),
            travpos, root == currnt ? currdepth : 0, qvars, root)});
        }
        else if (qvars != NULL && qvars->find(root->left()) != qvars->end())
        {
          // Root is a closed (quantified) variable
            travpos = TravPos(0, 1);
            ++travpos.pos;
            travpos.makedone();
            return ParseTree(root);
        }
        else
        {
          // There's no definition, we're expanding an empty *_VARS
          outs() << "ERROR: There is no definition for user-defined " <<
            "non-terminal " << root << " in the CFG for " << inv <<
            ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
          assert(0);
          return NULL;
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal
        travpos = TravPos(0, 1);
        ++travpos.pos;
        travpos.makedone();
        return ParseTree(root);
      }
      else
      {
        // Root is a Z3 function (e.g. (and ...))
        std::shared_ptr<ExprUSet> localqvars(new ExprUSet());
        vector<ParseTree> newexpr(root->arity());

        if (qvars != NULL)
          for (auto& var : *qvars)
            localqvars->insert(var);

        if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
        {
          // Add quantifier variables to qvars
          for (int i = 0; i < root->arity() - 1; ++i)
          {
            localqvars->insert(root->arg(i));
          }
        }

        // To reverse ('rtl'), we just invert newexpr and root->arg(i)
        function<ParseTree&(int)> newexprat;
        function<Expr(int)> rootarg;
        if (travdir == TravParamDirection::LTR)
        {
          newexprat = [&] (int i) -> ParseTree& { return newexpr[i]; };
          rootarg = [&] (int i) { return root->arg(i); };
        }
        else if (travdir == TravParamDirection::RTL)
        {
          newexprat = [&] (int i) -> ParseTree&
            { return newexpr[root->arity()-1-i]; };
          rootarg = [&] (int i) { return root->arg(root->arity()-1-i); };
        }

        if (travpos.pos < 0 && !travpos.inqueue())
        {
          // First-time initialize
          travpos = TravPos(0, root->arity());
          ++travpos.pos;

          if (travtype == TravParamType::STRIPED)
          {
            bool done = true;
            for (int i = 0; i < travpos.childrensize(); ++i)
            {
              newexprat(i) = newtrav(rootarg(i), travpos.childat(i),
                currdepth, qvars, currnt);
              bool idone = constpos.childat(i).isdone();
              if (idone && i == travpos.pos)
                ++travpos.pos;
              done &= idone;
            }
            if (done)
              travpos.makedone();

            return ParseTree(root, std::move(newexpr));
          }
        }

        // Traversal

        /*int start, end;
        function<bool(int)> cond;
        function<int(int)> nextpos;
        if (travdir == TravParamDirection::LTR)
        {
          start = 0;
          end = root->arity() - 1;
          cond = [&] (int i) { return i < root->arity(); };
          nextpos = [] (int i) { return i + 1; };
        }
        else if (travdir == TravParamDirection::RTL)
        {
          start = root->arity() - 1;
          end = 0;
          cond = [&] (int i) { return i >= 0; };
          nextpos = [] (int i) { return i - 1; };
        }*/

        if (travtype == TravParamType::STRIPED)
        {
          if (travpos.inqueue())
          {
            if (travpos.pos.limit == -1)
              travpos.pos = CircularInt(0, -1, travpos.queuesize());
            assert(travpos.pos.min == 0);
            ParseTree ret(NULL);
            ++travpos.pos;
            int startpos = travpos.pos;
            CircularInt checkpos = travpos.pos;
            while (constpos.queueat(checkpos).isdone())
            {
              ++checkpos;
              assert(checkpos != startpos);
            }
            travpos.pos = checkpos;

            ret = newtrav(root, travpos.queueat(travpos.pos),
              currdepth, qvars, currnt);

            bool done = true;
            checkpos = travpos.pos;
            for (int i = 0; i < constpos.queuesize(); ++i)
              done &= constpos.queueat(i).isdone();
            if (done)
            {
              if (travprio != TravParamPrio::BFS)
                travpos.makedone();
              else
              {
                for (int i = travpos.oldmin; i < travpos.childrensize(); ++i)
                  done &= constpos.childat(i).isdone();
                if (done)
                  travpos.makedone();
                else
                  travpos.makenotinqueue();
              }
            }

            assert(ret);

            return ret;
          }
          else if (travpos.pos.limit == -1)
          {
            travpos.pos = travpos.pos.min;
            travpos.pos.limit = root->arity();
            while (constpos.childat(travpos.pos).isdone())
            {
              ++travpos.pos;
              assert(travpos.pos != travpos.pos.min);
            }
            travpos.emptyqueue();
          }

          for (int i = 0; i < root->arity(); ++i)
          {
            if (i != travpos.pos)
            {
              assert(constpos.childat(i).pos >= 0);
              bool needdefer = false;
              if (travprio != TravParamPrio::DFS && i >= travpos.pos.min)
              {
                TravPos temppos;
                newexprat(i) = newtrav(rootarg(i), temppos,
                  currdepth, qvars, currnt);
              }
              else
                newexprat(i) = gettrav(rootarg(i), constpos.childat(i),
                  qvars, currnt, needdefer);
              if (needdefer)
              {
                if (constpos.childat(i).isdone())
                  travpos.childat(i) = TravPos();
                newexprat(i) = newtrav(rootarg(i), travpos.childat(i),
                  currdepth, qvars, currnt);
              }
            }
            else
            {
              assert(!constpos.childat(i).isdone());

              newexprat(i) = newtrav(rootarg(i), travpos.childat(i),
                currdepth, qvars, currnt);
              if (travpos.pos < root->arity() - 1)
              {
                bool done = true;
                for (int i = travpos.pos.min + 1; i < root->arity(); ++i)
                {
                  done &= constpos.childat(i).isdone();
                  if (!done)
                    break;
                }
                if (!done)
                {
                  TravPos *childpos = new TravPos(travpos, false);

                  childpos->pos = CircularInt(travpos.pos + 1,
                      travpos.pos + 1, root->arity());
                  int startpos = childpos->pos;
                  while (constpos.childat(childpos->pos).isdone())
                  {
                    ++childpos->pos;
                    assert(childpos->pos != startpos);
                  }

                  for (int i = travpos.pos.min; i < travpos.pos.limit; ++i)
                  {
                    if (i == travpos.pos)
                      continue;
                    childpos->childat(i) = TravPos();
                    newtrav(rootarg(i), childpos->childat(i),
                      currdepth, qvars, currnt);
                  }

                  travpos.queuepush_back(childpos);
                }
              }
            }
          }

          /*if (travdir == TravParamDirection::LTR)
            ++travpos.pos;
          else if (travdir == TravParamDirection::RTL)
            --travpos.pos;*/
          /*int startpos = travpos.pos;
          while (travpos.children[travpos.pos].isnextdone())
          {
            if (travdir == TravParamDirection::LTR)
              ++travpos.pos;
            else if (travdir == TravParamDirection::RTL)
              --travpos.pos;
            if (travpos.pos == startpos)
            {
              travpos.pos = root->arity();
              return NULL;
            }
          }*/

          if (travprio != TravParamPrio::DFS)
          {
            ++travpos.pos;
            if (travpos.pos == travpos.pos.min &&
            travprio == TravParamPrio::BFS &&
            constpos.queuesize() != 0)
              travpos.makeinqueue();
            else
            {
              int startpos = travpos.pos;
              while (constpos.childat(travpos.pos).isdone())
              {
                ++travpos.pos;
                if (travpos.pos == startpos)
                {
                  if (constpos.queuesize() != 0)
                    travpos.makeinqueue();
                  else
                  {
                    --travpos.pos;
                    travpos.makedone();
                  }
                  break;
                }
              }
            }
          }
          else if (constpos.childat(travpos.pos).isdone())
          {
            ++travpos.pos;
            if (travpos.pos == travpos.pos.min)
            {
              if (constpos.queuesize() != 0)
                travpos.makeinqueue();
              else
              {
                --travpos.pos;
                travpos.makedone();
              }
            }
            else
            {
              bool done = true;
              for (int i = travpos.pos.min; i < travpos.pos.limit; ++i)
                done &= constpos.childat(i).isdone();
              --travpos.pos;
              if (done)
              {
                travpos.makedone();
              }
              else
              {
                travpos.childat(travpos.pos) = TravPos();
                newtrav(rootarg(travpos.pos),
                  travpos.childat(travpos.pos), currdepth, qvars, currnt);
                ++travpos.pos;
              }
            }
          }
        }
        else if (travtype == TravParamType::ORDERED)
        {
          int di = 0;
          bool startreset = false;
          while (constpos.childat(di).isdone())
          {
            // Reset our position
            travpos.childat(di) = TravPos();
            newexprat(di) = newtrav(rootarg(di), travpos.childat(di),
              currdepth, qvars, currnt);
            if (di == 0)
              startreset = true;

            assert(di != root->arity() - 1);

            // Increment next position
            int nexti = di + 1;
            if (!constpos.childat(nexti).isdone())
            {
              newexprat(nexti) = newtrav(rootarg(nexti),
                travpos.childat(nexti), currdepth, qvars, currnt);
              break;
            }
            else
              di = nexti;
          }

          for (int i = di; i < root->arity(); ++i)
          {
            if (i != 0)
            {
              if (constpos.childat(i).pos < 0)
                newtrav(rootarg(i), travpos.childat(i), currdepth, qvars,
                  currnt);
              bool needdefer = false;
              newexprat(i) = gettrav(rootarg(i), constpos.childat(i), qvars,
                currnt, needdefer);
              if (needdefer)
              {
                if (constpos.childat(i).isdone())
                  travpos.childat(i) = TravPos();
                newexprat(i) = newtrav(rootarg(i), travpos.childat(i),
                  currdepth, qvars, currnt);
              }
            }
          }

          if (!startreset && !constpos.childat(0).isdone())
            newexprat(0) = newtrav(rootarg(0), travpos.childat(0),
              currdepth, qvars, currnt);

          bool done = true;
          for (int i = 0; i < root->arity(); ++i)
            done &= constpos.childat(i).isdone();
          if (done)
            travpos.makedone();
        }

        return ParseTree(root, newexpr);
      }
    }

    void getNextCandTrav_fn(coroutine<ParseTree>::push_type &sink,
        Expr root = NULL, int currdepth = 0,
        std::shared_ptr<ExprUSet> qvars = NULL, Expr currnt = NULL)
    {
      //currnumcandcoros++;
      if (root == NULL)
        root = inv;

      /*outs() << "getNextCandTrav(" << root << ", " << currdepth << ", ";
      if (qvars != NULL)
        printvec(outs(), *qvars);
      else
        outs() << "NULL";
      outs() << ", " << currnt << ")" << endl;*/

      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const varset &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          sink(ParseTree(root));
          //currnumcandcoros--;
          return;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname == "either")
        {
          vector<int> order;

          if (travorder == TravParamOrder::FORWARD)
            for (int i = 1; i < root->arity(); ++i)
            {
              if (!isRecursive(root->arg(i), currnt) ||
              currdepth + 1 <= maxrecdepth)
                order.push_back(i);
            }
          else if (travorder == TravParamOrder::REVERSE)
            for (int i = root->arity() - 1; i >= 1; --i)
            {
              if (!isRecursive(root->arg(i), currnt) ||
              currdepth + 1 <= maxrecdepth)
                order.push_back(i);
            }
          else if (travorder == TravParamOrder::RND)
          {
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
          }

          if (order.size() == 0)
          {
            sink(NULL);
            return;
          }

          // First: Production, Second: Coroutine
          list<std::pair<std::pair<Expr,Expr>,PTCoroCacheIter>> coros;
          for (int i : order)
          {
            int newdepth;
            if (isRecursive(root->arg(i), currnt))
              newdepth = currdepth + 1;
            else
              newdepth = currdepth;

            coros.push_back(std::move(make_pair(make_pair(root->arg(i),
              currnt), getCandCoro(root->arg(i), newdepth, qvars,currnt))));
            if (!*coros.back().second)
              coros.pop_back();
            else if (travtype == TravParamType::STRIPED)
            {
              sink(*coros.back().second);
              ++coros.back().second;
              if (!coros.back().second)
                coros.pop_back();
            }
          }

          auto lastbest = coros.begin();

          // Key: <Production, Non-terminal>,
          // Value: number of cands generated with Production
          unordered_map<std::pair<Expr, Expr>, int> candnum;
          int totalcandnum = 0;


          // prod has same format as Key of candnum
          auto shoulddefer = [&] (const std::pair<Expr,Expr>& prod) -> bool
          {
            if (candnum[prod] == 0 || priomap[prod] == 1)
              return false;
            return candnum[prod] > (int)(priomap[prod]*totalcandnum);
          };

          for (auto &kv : coros)
          {
            candnum[kv.first] = 0;
          }

          while (coros.size() != 0)
          {
            bool didsink = false;

            if (travtype == TravParamType::ORDERED)
            {
              auto itr = coros.begin();
              if (coros.size() != 0 && itr != coros.end())
              {
                while (itr != coros.end() && shoulddefer(itr->first))
                  ++itr;

                if (itr != coros.end())
                {
                  sink(*itr->second);
                  candnum[itr->first]++;
                  ++itr->second;
                  if (!itr->second)
                  {
                    itr = coros.erase(itr);
                    lastbest = coros.begin();
                  }
                  didsink = true;
                }
              }
            }
            else if (travtype == TravParamType::STRIPED)
            {
              for (auto itr = coros.begin(); itr != coros.end();)
              {
                if (shoulddefer(itr->first))
                {
                  ++itr;
                  continue;
                }

                sink(*itr->second);
                didsink = true;
                candnum[itr->first]++;
                ++itr->second;
                if (!itr->second)
                {
                  auto olditr = itr;
                  itr = coros.erase(itr);
                  if (lastbest == olditr)
                    lastbest = coros.begin();
                  continue;
                }
                ++itr;
              }
            }

            if (coros.size() != 0 && !didsink)
            {
              // No coroutines available, pick best option.
              if (!lastbest->second)
                lastbest = coros.begin();
              auto bestcoro = lastbest;
              bool setbestcoro = false;
              for (auto itr = coros.begin(); itr != lastbest; ++itr)
              {
                if (priomap[itr->first] > priomap[bestcoro->first])
                {
                  bestcoro = itr;
                  setbestcoro = true;
                }
              }

              if (!setbestcoro)
              {
                auto itr = lastbest;
                if (travtype == TravParamType::STRIPED)
                  ++itr;
                for (; itr != coros.end(); ++itr)
                {
                  if (priomap[itr->first] >= priomap[bestcoro->first])
                  {
                    bestcoro = itr;
                    setbestcoro = true;
                    break;
                  }
                }
              }

              sink(*bestcoro->second);
              candnum[bestcoro->first]++;
              ++bestcoro->second;
              if (!bestcoro->second)
              {
                auto oldbestcoro = bestcoro;
                bestcoro = coros.erase(bestcoro);
                if (lastbest == oldbestcoro)
                  lastbest = coros.begin();
                continue;
              }
            }
          }

          //currnumcandcoros--;
          return;
        }
        else
        {
          // Root is user-defined non-terminal
          if (defs[root] != NULL)
          {
            //currnumcandcoros--;
            PTCoroCacheIter newcoro = getCandCoro(defs[root], root == currnt ?
              currdepth : 0, qvars, root);
            for (ParseTree pt : newcoro)
            {
              sink(ParseTree(root, vector<ParseTree>{pt}));
            }
            return;
          }
          else if (qvars != NULL &&
          qvars->find(root->first()) != qvars->end())
          {
              // Root is a variable for a surrounding quantifier
              sink(ParseTree(root));
              //currnumcandcoros--;
              return;
          }
          else
          {
            // There's no definition, we're expanding an empty *_VARS
            outs() << "ERROR: There is no definition for user-defined " <<
              "non-terminal " << root << " in the CFG for " << inv <<
              ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
            assert(0);
          }
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        sink(ParseTree(root));
        //currnumcandcoros--;
        return;
      }

      // Root is Z3-defined non-terminal

      std::shared_ptr<ExprUSet> localqvars(new ExprUSet());

      if (qvars != NULL)
        for (auto& var : *qvars)
          localqvars->insert(var);

      if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      {
        // Add quantifier variables to qvars
        for (int i = 0; i < root->arity() - 1; ++i)
        {
          localqvars->insert(root->arg(i));
        }
      }

      // The set of Expr's we'll use to generate this n-ary expression.
      vector<ParseTree> expanded_args;
      // The corresponding coroutines for each entry in expanded_args.
      vector<optional<PTCoroCacheIter>> argcoros;

      // Initialize all arguments to valid Expr's;
      //   otherwise we can't do mkNary below.
      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
      {
        if (travtype == TravParamType::ORDERED)
        {
          argcoros.push_back(boost::none);
          expanded_args.push_back(NULL);
        }
        else
        {
          argcoros.push_back(getCandCoro(*itr,currdepth,localqvars,currnt));
          expanded_args.push_back(argcoros.back()->get());
          (*argcoros.back())();
        }
      }

      // Traversal of root done.
      //currnumcandcoros--;
      return travCand_fn(sink, std::move(argcoros), std::move(expanded_args),
        std::move(set<int>()), root, currdepth, localqvars, currnt);
    }
    PTCoroCacheIter getCandCoro(Expr root = NULL, int currdepth = 0,
      std::shared_ptr<ExprUSet> qvars = NULL, Expr currnt = NULL)
    {
      std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr> tup =
        make_tuple(root, currdepth, qvars, currnt);
      bool didemplace = false;
      if (ptcorocache.find(tup) == ptcorocache.end())
      {
        ptcorocache.emplace(tup, std::move(PTCoroCache(std::move(
          PTCoro(std::bind(&GRAMfactory::getNextCandTrav_fn, this,
          std::placeholders::_1, root, currdepth, qvars, currnt))))));
        didemplace = true;
      }
      return ptcorocache.at(tup).begin();
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

    void travCand_fn(coroutine<ParseTree>::push_type& sink,
        vector<optional<PTCoroCacheIter>> coros, vector<ParseTree> cand,
        set<int> stuck, Expr root, int currdepth,
        std::shared_ptr<ExprUSet> qvars, Expr currnt)
    {
      //currnumtravcoros[root]++;
      /*outs() << "travCand_fn([";
      for (auto &opt : coros)
      {
        if (opt)
          outs() << " " << &*opt;
        else
          outs() << " none";
      }
      outs() << " ], ";
      printvec(outs(), cand);
      outs() << ", ";
      printvec(outs(), stuck);
      outs() << ")" << endl;*/
      if (travtype == TravParamType::STRIPED ||
      stuck.size() == cand.size())
        //sink(m_efac.mkNary(root->op(), cand));
        sink(ParseTree(root, cand));

      if (stuck.size() == cand.size())
        return;

      vector<PTCoro> methcoros;
      auto emptymethcoros = [&] () {
        bool methcoroavail = true;
        while (methcoroavail)
        {
          methcoroavail = false;
          for (auto& meth : methcoros)
          {
            if (meth)
            {
              sink(meth.get());
              meth();
              methcoroavail = true;
            }
          }
        }
        methcoros.clear();
      };

      if (travtype == TravParamType::STRIPED)
      {
        vector<int> free;
        int min_i = 0, max_i = coros.size();
        if (stuck.size() != 0)
          min_i = *(--stuck.end()) + 1;
        if (travdir == TravParamDirection::LTR)
          for (int i = min_i; i < max_i; ++i)
            free.push_back(i);
        else if (travdir == TravParamDirection::RTL)
          for (int i = max_i - 1; i >= min_i; --i)
            free.push_back(i);

        if (travdir == TravParamDirection::RND)
          random_shuffle(free.begin(), free.end());

        auto inloopfn = [&] (int pos) -> bool {
          if (!*coros[pos])
            return false;

          vector<ParseTree> newcand = cand;
          newcand[pos] = coros[pos]->get();
          (*coros[pos])();
          /*if (pos == 1 &&
          (isOpX<MOD>(root) || isOpX<DIV>(root) || isOpX<IDIV>(root)))
          {
            Expr posexpr = collapsePT(newcand[pos]);
            bool doexit = false;
            while (isOpX<MPZ>(posexpr) &&
            isOpX<MOD>(root) ? lexical_cast<cpp_int>(posexpr) <= 0 :
            lexical_cast<cpp_int>(posexpr) == 0)
            {
              if (doexit)
                return false;
              newcand[pos] = coros[pos]->get();
              posexpr = collapsePT(newcand[pos]);
              if (*coros[pos])
                (*coros[pos])();
              else
                doexit = true;
            }
          }*/
          set<int> newstuck = stuck;
          for (int i = 0; i <= pos; ++i)
            newstuck.insert(i);

          if (newstuck.size() == newcand.size())
            //sink(m_efac.mkNary(root->op(), newcand));
            sink(ParseTree(root, newcand));
          else
          {
            vector<optional<PTCoroCacheIter>> newcoros;
            for (int i = 0; i < coros.size(); ++i)
            {
              if (newstuck.find(i) == newstuck.end())
              {
                newcoros.push_back(getCandCoro(root->arg(i), currdepth,
                    qvars, currnt));
                newcand[i] = newcoros[i]->get();
                (*newcoros[i])();
              }
              else
                newcoros.push_back(boost::none);
            }

            methcoros.push_back(getTravCoro(std::move(newcoros),
              std::move(newcand), std::move(newstuck), root, currdepth, qvars,
              currnt));
            sink(methcoros.back().get());
            methcoros.back()();
          }

          return true;
        };

        if (travprio != TravParamPrio::DFS)
        {
          bool coroavail = true;
          while (coroavail)
          {
            coroavail = false;
            for (int i : free)
              coroavail |= inloopfn(i);
            if (travprio == TravParamPrio::BFS)
              emptymethcoros();
          }
        }
        else
        {
          for (int i : free)
          {
            bool coroavail = true;
            while (coroavail)
              coroavail = inloopfn(i);
          }
        }
      }
      else if (travtype == TravParamType::ORDERED)
      {
        vector<int> free;
        for (int i = 0; i < cand.size(); ++i)
          if (stuck.find(i) == stuck.end())
            free.push_back(i);

        int nextstuck;
        if (travdir == TravParamDirection::LTR)
          nextstuck = free.back();
        else if (travdir == TravParamDirection::RTL)
          nextstuck = free.front();
        else if (travdir == TravParamDirection::RND)
          nextstuck = free[rand() % free.size()];

        PTCoroCacheIter nextcoro = getCandCoro(root->arg(nextstuck),
          currdepth, qvars, currnt);

        set<int> newstuck = stuck;
        newstuck.insert(nextstuck);

        for (ParseTree exp : nextcoro)
        {
          cand[nextstuck] = exp;

          /*if (nextstuck == 1 &&
            (isOpX<MOD>(root) || isOpX<DIV>(root) || isOpX<IDIV>(root)))
          {
            Expr posexpr = collapsePT(cand[nextstuck]);
            if (isOpX<MPZ>(posexpr) &&
            isOpX<MOD>(root) ? lexical_cast<cpp_int>(posexpr) <= 0 :
            lexical_cast<cpp_int>(posexpr) == 0)
              continue;
          }*/

          vector<optional<PTCoroCacheIter>> newcoros;
          for (int i = 0; i < coros.size(); ++i)
            newcoros.push_back(boost::none);

          if (newstuck.size() == cand.size())
            //sink(m_efac.mkNary(root->op(), cand));
            sink(ParseTree(root, cand));
          else
          {
            PTCoro newmeth = getTravCoro(std::move(newcoros), cand,
              newstuck, root, currdepth, qvars, currnt);
            for (ParseTree exp : newmeth)
              sink(exp);
          }
        }
      }

      emptymethcoros();
      //currnumtravcoros[root]--;
    }

    PTCoro getTravCoro(vector<optional<PTCoroCacheIter>> coros,
      vector<ParseTree> cand, set<int> stuck, Expr root, int currdepth,
      std::shared_ptr<ExprUSet> qvars, Expr currnt)
    {
      // We can't use std::bind, since that will try to copy coros
      return std::move(PTCoro([&] (coroutine<ParseTree>::push_type &sink) {
        return travCand_fn(sink, std::move(coros), std::move(cand),
          std::move(stuck), root, currdepth, qvars, currnt); }));
    }

    // qvars is set of quantifier variables for this expression.
    // Using pointer because we need it to be nullable.
    Expr getRandCand(Expr root, ExprUSet *qvars = NULL)
    {
      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const varset &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          return root;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname == "either")
        {
          Expr cand = NULL;
          while (cand == NULL)
          {
            // Randomly select from the available productions.
            // Offset by 1 because arg(0) is the fdecl.
            //int randindex = (rand() % (root->arity() - 1)) + 1;
            int randindex = distmap[root](randgenerator) + 1;

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
            assert(0);
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
      m_efac(_efac), z3(_z3), m_smt_solver(z3),
      printLog(_printLog), inv(NULL), getNextCandTrav(nullptr) {}

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
      int_consts.insert(iconst);
    }

    void setParams(GramParams params)
    {
      std::tie(genmethod, maxrecdepth, travdir, travorder, travtype,
          travprio, b4simpl, timeout) = params;
      ZParams<EZ3> zp(z3);
      zp.set("timeout", timeout);
      m_smt_solver.set(zp);
    }

    GramParams getParams()
    {
      return std::move(std::make_tuple(genmethod, maxrecdepth, travdir,
            travorder, travtype, travprio, b4simpl, timeout));
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

        // The provided grammar, plus variable definitions and special
        //   variables that we define.
        ostringstream aug_gram;

        auto generate_sort_decls = [&] (const string& sort_name,
        const string& sort_smt, const string& vars_name)
        {
            // Generate either functions for given sort
            for (int i = 1; i <= NUMEITHERS; ++i)
            {
              auto gensorts = [&] ()
              {
                for (int x = 1; x <= i; ++x)
                {
                  aug_gram << sort_smt << " ";
                }
              };
              aug_gram << "(declare-fun either ( ";
              gensorts();
              aug_gram << ") " << sort_smt << ")\n";

              // Generate n-ary `equal` constraint declarations
              aug_gram << "(declare-fun equal (";
              gensorts();
              aug_gram << ") Bool)\n";

              // Generate n-ary `equal_under` constraint declarations
              aug_gram << "(declare-fun equal_under ( String ";
              gensorts();
              aug_gram << ") Bool)\n";

              // Generate n-ary `distinct_under` constraint declarations
              aug_gram << "(declare-fun distinct_under ( String ";
              gensorts();
              aug_gram << ") Bool)\n";
            }

            // Special *_VARS variable
            aug_gram << "(declare-fun " << vars_name << " () " <<
              sort_smt << ")\n";
            // Generate *_prio declarations
            aug_gram << "(declare-fun prio (" <<
              sort_smt << " Real) " << sort_smt << ")\n";

            // Generate binary `expands` constraint declarations
            aug_gram << "(declare-fun expands ("<<sort_smt<<" String) Bool)\n";

            // Generate binary `under` constraint declarations
            aug_gram << "(declare-fun under (String "<<sort_smt<<") Bool)\n";
        };

        // We need the Bool eithers for the inv definition (rel is Bool)
        generate_sort_decls("Bool", "Bool", "BOOL_VARS");

        // Which sorts we've already generated eithers and *_VARS for.
        ExprSet donesorts;
        donesorts.insert(mk<BOOL_TY>(m_efac));

        // Easiest way to handle all_inv_vars and inv_vars
        auto generate_all = [&] (unordered_map<Expr, varset> vars,
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

            string vars_name(sort_name);
              vars_name += "_VARS";
            for (auto& c : vars_name)
              c = (char)toupper(c);

            // If we haven't already generated an either
            if (donesorts.find(pair.first) == donesorts.end())
            {
              generate_sort_decls(sort_name, sort_smt, vars_name);
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
                  " (either";

                for (auto& var : pair.second)
                {
                  aug_gram << " " << var;
                }

                aug_gram << ")))" << endl;
              }
              else if (pair.second.size() == 1)
              {
                aug_gram << "(assert (= " << vars_name << " " <<
                  *pair.second.begin() << "))" << endl;
              }
            }
          }
        };

        generate_all(inv_vars, true);
        generate_all(other_inv_vars, false);

        // Generate INT_CONSTS declaration
        aug_gram << "(declare-fun " << INT_CONSTS << " () Int)\n";

        aug_gram << "(declare-fun constraint (Bool) Bool)\n";
        aug_gram << "(declare-fun constraint_any (Bool) Bool)\n";

        // Generate unary `present` constraint declarations
        aug_gram << "(declare-fun present (String) Bool)\n";

        // Generate unary `maxrecdepth` function declaration
        aug_gram << "(declare-fun maxrecdepth (String) Int)\n";

        aug_gram << user_cfg.str();

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

            if (isOpX<FAPP>(ex->right()) &&
            lexical_cast<string>(bind::fname(ex->right())->left())=="either")
            {
              ExprVector newdefargs;
              vector<cpp_rational> rweights;
              for (auto itr = ++ex->right()->args_begin();
              itr != ex->right()->args_end(); ++itr)
              {
                if (isOpX<FAPP>(*itr) &&
                lexical_cast<string>(bind::fname(*itr)->left()) == "prio")
                {
                  std::pair<Expr,Expr> keypair(ex->left(), (*itr)->arg(1));
                  auto prio = lexical_cast<cpp_rational>((*itr)->arg(2));
                  priomap[keypair] = prio;
                  rweights.push_back(prio);
                  newdefargs.push_back((*itr)->arg(1));
                }
                else
                {
                  std::pair<Expr, Expr> keypair(ex->left(), *itr);
                  priomap[keypair] = 1;
                  rweights.push_back(1);
                  newdefargs.push_back(*itr);
                }
              }

              // Simple GCD, to make sure all priorities convert to integers
              int gcd = 1;
              for (auto &rw : rweights)
                gcd *= (int)denominator(rw);

              vector<int> iweights;
              for (auto &rw : rweights)
                iweights.push_back((int)(rw * gcd));

              Expr newright = bind::fapp(ex->right()->left(), newdefargs);

              distmap.emplace(newright,
                std::move(discrete_distribution<int>(iweights.begin(),
                iweights.end())));

              defs[ex->left()] = newright;
            }
            else
              defs[ex->left()] = ex->right();
          }
          else if (isOpX<FAPP>(ex))
          {
            string ename = lexical_cast<string>(bind::fname(ex)->left());
            if (ename == "constraint" || ename == "constraint_any")
            {
              constraints.push_back(ex);

              // Parse strings in Z3 now
              function<void(Expr)> visitExpr = [&] (Expr e)
              {
                if (isOpX<STRING>(e) && strcache.count(e) == 0)
                {
                  string estr = lexical_cast<string>(e);
                  estr = aug_gram.str() + "\n(assert (= "+estr+" "+estr+"))\n";
                  Expr ret = z3_from_smtlib<EZ3>(z3, estr);
                  strcache.emplace(e, ret->arg(ret->arity() - 1)->arg(0));
                }
                else
                  for (int i = 0; i < e->arity(); ++i)
                  {
                    if (isOpX<FDECL>(e->arg(i)))
                      continue;
                    visitExpr(e->arg(i));
                  }
              };
              visitExpr(ex);
            }
          }
        }
      }

      initialized = (inv != NULL);

      if (printLog)
      {
        for (const auto& p : priomap)
          outs() << "priomap[<" << p.first.first << ", " <<
            p.first.second << ">]: " << p.second << "\n";
        for (const auto& d : distmap)
          outs() << "distmap[" << d.first << "]: " << d.second << "\n";
      }

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
        Expr eitherfunc = bind::fdecl(mkTerm(string("either"), m_efac),
            ExprVector(int_consts.size(), m_efac.mkTerm(INT_TY())));

        Expr int_consts_decl = bind::intConst(mkTerm(string(INT_CONSTS), m_efac));
        ExprVector exprconsts;
        for (const auto &iconst : int_consts)
          exprconsts.push_back(mkMPZ(iconst, m_efac));
        defs[int_consts_decl] = bind::fapp(eitherfunc, exprconsts);
      }

      if (initialized && genmethod == GramGenMethod::TRAV)
      {
        std::shared_ptr<ExprUSet> qvars = NULL;
        int currdepth = 0;
        Expr currnt = NULL;
        getNextCandTrav = std::unique_ptr<PTCoro>(new PTCoro(
            std::bind(&GRAMfactory::getNextCandTrav_fn, this,
            std::placeholders::_1, inv, currdepth, qvars, currnt)));
      }
    }

    static void printPT(ParseTree pt, int depth = 0)
    {
      for (int i = 0; i < depth; ++i) outs() << "  ";
      outs() << pt.data() << "\n";
      for (auto &p : pt.children())
        printPT(p, depth + 1);
    }

    Expr getFreshCandidate()
    {
      if (inv == NULL)
        return NULL; // Should never happen, but handle just in case

      Expr nextcand = NULL;
      ParseTree nextpt = NULL;

      /*for (auto& kv : currnumtravcoros)
        outs() << "currnumtravcoros[" << kv.first << "] = " << kv.second << "\n";
      outs() << "currnumcandcoros = " << currnumcandcoros << "\n";*/

      // Generate a new candidate from the grammar, and simplify
      while (!nextcand)
      {
        if (genmethod == GramGenMethod::TRAV)
        {
          if (!*getNextCandTrav)
          {
            outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
            done = true;
            //exit(0);
            return NULL;
          }

          nextpt = getNextCandTrav->get();
          nextcand = collapsePT(nextpt);
          (*getNextCandTrav)();
        }
        else if (genmethod == GramGenMethod::NEWTRAV)
        {
          if (rootpos.isdone())
          {
            outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
            done = true;
            //exit(0);
            return NULL;
          }
          nextpt = newtrav(inv, rootpos);
          //printPT(nextpt);
          nextcand = collapsePT(nextpt);

          // Update candnum and totalcandnum
          foreachExp(nextpt, [&] (const Expr& nt, const Expr& prod)
            {
              candnum[make_pair(nt, prod)]++;
            });
          totalcandnum++;
        }
        else if (genmethod == GramGenMethod::RND)
        {
          nextcand = getRandCand(inv);
        }

        nextpt.fixchildren();

        if (b4simpl)
          outs() << "Before simplification: " << nextcand << endl;
        nextcand = simplifyBool(simplifyArithm(nextcand));
        if (isOpX<TRUE>(nextcand) || isOpX<FALSE>(nextcand))
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Tautology/Contradiction" << endl;
        }
        else if (constraints.size() != 0 && !doesSatConstraints(nextpt))
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Doesn't satisfy constraints" << endl;
        }
        else if (!gramCands.insert(nextcand).second)
        {
          nextcand = NULL;
          nextpt = NULL;
          if (b4simpl)
            outs() << "Old candidate" << endl;
        }
        else
        {
          if (gramCandsOrder.size() == MAXGRAMCANDS)
          {
            gramCands.erase(gramCandsOrder[0]);
            gramCandsOrder.pop_front();
          }
          gramCandsOrder.push_back(nextcand);
          break;
        }
      }

      return nextcand;
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
      if (!strcmp(methodstr, "newtrav"))
        return GramGenMethod::NEWTRAV;

      outs() << "Error: Unrecognized --gen_method \"" << methodstr << "\"" << endl;
      exit(1);
      return GramGenMethod::RND;
    }
    static TravParamDirection strtotravdir(const char* str)
    {
      if (!strcmp(str, "ltr"))
        return TravParamDirection::LTR;
      if (!strcmp(str, "rtl"))
        return TravParamDirection::RTL;
      if (!strcmp(str, "rnd"))
        return TravParamDirection::RND;

      outs() << "Error: Unrecognized --trav_direction \"" << str << "\"" << endl;
      exit(1);
      return TravParamDirection::LTR;
    }
    static TravParamOrder strtotravord(const char* str)
    {
      if (!strcmp(str, "forward"))
        return TravParamOrder::FORWARD;
      if (!strcmp(str, "reverse"))
        return TravParamOrder::REVERSE;
      if (!strcmp(str, "rnd"))
        return TravParamOrder::RND;

      outs() << "Error: Unrecognized --trav_order \"" << str << "\"" << endl;
      exit(1);
      return TravParamOrder::FORWARD;
    }
    static TravParamType strtotravtype(const char* str)
    {
      if (!strcmp(str, "ordered"))
        return TravParamType::ORDERED;
      if (!strcmp(str, "striped"))
        return TravParamType::STRIPED;

      outs() << "Error: Unrecognized --trav_type \"" << str << "\"" << endl;
      exit(1);
      return TravParamType::STRIPED;
    }
    static TravParamPrio strtotravprio(const char* str)
    {
      if (!strcmp(str, "sfs"))
        return TravParamPrio::SFS;
      if (!strcmp(str, "bfs"))
        return TravParamPrio::BFS;
      if (!strcmp(str, "dfs"))
        return TravParamPrio::DFS;

      outs() << "Error: Unrecognized --trav_priority \"" << str << "\"" << endl;
      exit(1);
      return TravParamPrio::SFS;
    }
  };
}

#endif
