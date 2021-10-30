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
    
    class ParseTreeNode;
    class ParseTree;

    // A coroutine returning a ParseTree.
    typedef coroutine<ParseTree>::pull_type PTCoro;

    class ParseTreeNode
    {
      private:

      // Will be FAPP or terminal (MPZ, _FH_inv_0, etc.)
      Expr data;
      // Shape will match data; if data has 3 args, children will have 3 args,
      //   even if some of the arguments are e.g. terminals.
      // children[0] == expansion of data.arg(1), etc.
      vector<ParseTree> children;

      ParseTreeNode(Expr _data, const vector<ParseTree>& _children) :
        data(_data), children(_children) {}

      ParseTreeNode(Expr _data, vector<ParseTree>&& _children) :
        data(_data), children(_children) {}

      ParseTreeNode(Expr _data) : data(_data)
      {
        assert(("Must pass a vector of children for non-FAPP Expr with arity != 0",
          data->arity() == 0 || isOpX<FAPP>(data)));
      }

      friend ParseTree;
    };

    class ParseTree
    {
      std::shared_ptr<ParseTreeNode> ptr;

      public:
      ParseTree(Expr _data, const vector<ParseTree>& _children) :
        ptr(new ParseTreeNode(_data, _children)) {}

      ParseTree(Expr _data, vector<ParseTree>&& _children) :
        ptr(new ParseTreeNode(_data, _children)) {}
      ParseTree(const ParseTree& pt) : ptr(pt.ptr) {}
      ParseTree(ParseTreeNode* ptptr) : ptr(ptptr) {}
      ParseTree(Expr _data) : ptr(new ParseTreeNode(_data)) {}
      ParseTree() : ptr(NULL) {}

      const Expr& data() const
      {
        return ptr->data;
      }

      const vector<ParseTree>& children() const
      {
        return ptr->children;
      }

      operator bool()
      {
        return bool(ptr);
      }

      /*operator Expr()
      {
        return ptr ? ptr->data : NULL;
      }

      operator cpp_int()
      {
        return lexical_cast<cpp_int>(ptr->data);
      }*/
    };

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

    class pairhash
    {
      public:
      size_t operator()(const std::pair<Expr,Expr>& pr) const
      {
        return std::hash<Expr>()(pr.first) * std::hash<Expr>()(pr.second);
      }
    };

    struct TravPos;

    struct CircularInt
    {
      public:
      // min <= val < limit
      int min, val, limit;
      
      CircularInt() : min(0), val(-1), limit(0) {}
      CircularInt(int _min, int _val, int _limit) :
        min(_min), val(_val), limit(_limit) {}
      CircularInt(const CircularInt& copy) :
        min(copy.min), val(copy.val), limit(copy.limit) {}

      inline operator int() const
      {
        return val;
      }

      CircularInt& operator=(const CircularInt& copy)
      {
        min = copy.min;
        val = copy.val;
        limit = copy.limit;
        return *this;
      }

      CircularInt& operator=(int other)
      {
        // Purposefully ignore limits.
        val = other;
        return *this;
      }

      CircularInt& operator++()
      {
        if (val < min || val >= limit)
          val = min;
        else
        {
          val++;
          if (val >= limit)
            val = min;
        }
        return *this;
      }

      CircularInt operator++(int)
      {
        CircularInt old = *this;
        ++(*this);
        return old;
      }

      CircularInt& operator--()
      {
        if (val >= limit || val < min)
          val = limit - 1;
        else
        {
          val--;
          if (val < min)
            val = limit - 1;
        }
        return *this;
      }

      CircularInt operator--(int)
      {
        CircularInt old = *this;
        --(*this);
        return old;
      }

      friend TravPos;
    };

    struct TravPos
    {
      private:
      // Pair is <we_own, object>; we_own is true if we can modify w/o CoW
      vector<pair<bool,TravPos*>> children;
      deque<pair<bool,TravPos*>> queue; // For STRIPED traversal
      bool readonly = false;

      void copyother(const TravPos& copy, bool copyqueue)
      {
        pos = copy.pos;
        children.reserve(copy.children.size());
        for (auto &child : copy.children)
          children.push_back(std::move(make_pair(false, child.second)));
        if (copyqueue)
        {
          oldmin = copy.oldmin;
          for (auto &que : copy.queue)
            queue.push_back(std::move(make_pair(false, que.second)));
        }
      }

      public:
      CircularInt pos;
      int oldmin = -1;

      TravPos() {}

      TravPos(int min, int limit) : pos(min, -1, limit)
      {
        children.reserve(limit);
        for (int i = 0; i < limit; ++i)
          children.push_back(std::move(make_pair(true, new TravPos())));
      }

      TravPos(const TravPos& copy)
      {
        copyother(copy, true);
      }

      TravPos(TravPos& copy, bool copyqueue = true)
      {
        // If child is read-only, we can do a const-copy.
        if (copy.readonly)
          copyother((const TravPos&)copy, copyqueue);
        else
        {
          // Can't just set realpos to &copy; if copy changes any of its
          //   values, ours will change too (NOT what we want).
          //   Thus, we create a new (read-only) common ancestor with copy's
          //   data, and make a CoW clone of that. This necessitates changing
          //   copy, of course.

          const TravPos *ropos = new TravPos(std::move(copy));
          for (auto &child : ropos->children)
            if (child.first)
              child.second->readonly = true;
          for (auto &que : ropos->queue)
            if (que.first)
              que.second->readonly = true;
          copy.~TravPos();
          new (&copy) TravPos(*ropos);
          copyother(*ropos, copyqueue);
        }
      }

      TravPos(TravPos&& move) : pos(move.pos),
        children(std::move(move.children)), queue(std::move(move.queue)),
        oldmin(move.oldmin) {}

      ~TravPos()
      {
        // Only deallocate any memory we own.
        for (auto &child : children)
          if (child.first)
            delete child.second;
        for (auto &que : queue)
          if (que.first)
            delete que.second;
      }

      TravPos& operator=(const TravPos& copy)
      {
        this->~TravPos();
        new (this) TravPos(copy);
        return *this;
      }
      TravPos& operator=(TravPos& copy)
      {
        this->~TravPos();
        new (this) TravPos(copy);
        return *this;
      }
      TravPos& operator=(TravPos&& move)
      {
        this->~TravPos();
        // Necessary std::move; calls copy c-tor without
        new (this) TravPos(std::move(move));
        return *this;
      }

      inline const TravPos& childat(int pos) const
      {
        return *children[pos].second;
      }

      inline TravPos& childat(int pos)
      {
        if (!children[pos].first)
          children[pos] = std::move(
            make_pair(true, new TravPos(*children[pos].second)));
        return *children[pos].second;
      }

      inline int childrensize() const
      {
        return children.size();
      }

      inline const TravPos& queueat(int pos) const
      {
        return *queue[pos].second;
      }

      inline TravPos& queueat(int pos)
      {
        if (!queue[pos].first)
          queue[pos] = std::move(
            make_pair(true, new TravPos(*queue[pos].second)));
        return *queue[pos].second;
      }

      inline int queuesize() const
      {
        return queue.size();
      }

      inline void queuepush_back(TravPos* newpos)
      {
        // Takes ownership of newpos
        return queue.push_back(std::move(make_pair(true, newpos)));
      }

      inline void emptyqueue()
      {
        queue.clear();
      }

      inline bool isdone() const
      {
        return pos.min == -1;
      }

      inline void makedone()
      {
        pos.min = -1;
      }

      inline bool inqueue() const
      {
        return oldmin != -1;
      }

      inline void makeinqueue()
      {
        pos.limit = -1;
        oldmin = pos.min;
      }

      inline void makenotinqueue()
      {
        pos.min = oldmin;
        pos.limit = -1;
        oldmin = -1;
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
    unordered_map<std::pair<Expr, Expr>, cpp_rational, pairhash> priomap;

    // priomap, but for getRandCand
    // Key: Non-terminal, Value: Distribution, in order given by CFG
    unordered_map<Expr, discrete_distribution<int>> distmap;

    // Needed for randomness in getRandCand
    default_random_engine randgenerator;

    // Key: <Non-terminal, Production>
    // Value: number of candidates generated with NT->Prod expansion
    unordered_map<std::pair<Expr,Expr>,int,pairhash> candnum;

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
      if (pt.children().size() == 1)
        return collapsePT(pt.children()[0]);
      else if (pt.children().size() == 0)
        return pt.data();
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

    inline void foreachExp(const ParseTree& pt,
      const function<void(const Expr&, const Expr&)>& func)
    {
      if (pt.children().size() == 0)
        return;
      else if (pt.children().size() == 1)
      {
        const ParseTree* realnt = &pt;
        while (defs.count(realnt->children()[0].data()) != 0)
          realnt = &realnt->children()[0];

        func(pt.data(), realnt->children()[0].data());

        return foreachExp(pt.children()[0], func);
      }
      else
      {
        for (auto &subpt : pt.children())
          foreachExp(subpt, func);
      }
    }

    // Key: Non-terminal   Value: Set of Expr's that First expands to
    // `notselfdist` is a set of non-terminals which aren't distinct within
    //   themselves (i.e., there are two expansions of the non-terminal to
    //   the same value within the expression).
    // `notselfeq` is inverse of set of non-terminals for which all
    //   expansions are equivalent (e.g. all INT_CONSTS expand to 2)
    void findExpansions(const ParseTree& pt,
        unordered_map<Expr,ExprUSet>& outmap, ExprUSet& notselfdist,
        ExprUSet& notselfeq)
    {
      return foreachExp(pt, [&] (const Expr& nt, const Expr& prod)
        {
          if (!outmap[nt].insert(prod).second)
            notselfdist.insert(nt);
          else if (outmap[nt].size() != 1)
            notselfeq.insert(nt);
        });
    }

    inline static tribool evaluateCmpExpr(Expr cmp)
    {
      // simplifyArithm is also simplifying comparisons
      if (isOpX<FALSE>(cmp))
        return false;
      if (isOpX<TRUE>(cmp))
        return true;
      if (isOpX<NEG>(cmp))
        return !evaluateCmpExpr(cmp->left());
      if (isOpX<EQ>(cmp))
      {
        if (!isOpX<FAPP>(cmp->arg(0)) && !isOpX<MPZ>(cmp->arg(0)) &&
        !isOpX<MPQ>(cmp->arg(0)))
          return indeterminate;
        for (int i = 1; i < cmp->arity(); ++i)
        {
          if (!isOpX<FAPP>(cmp->arg(i)) && !isOpX<MPZ>(cmp->arg(i)) &&
          !isOpX<MPQ>(cmp->arg(i)))
            return indeterminate;
          if (cmp->arg(i) != cmp->arg(0))
            return false;
        }
        return true;
      }
      if (isOpX<NEQ>(cmp))
      {
        for (int p1 = 0; p1 < cmp->arity(); ++p1)
          for (int p2 = p1 + 1; p2 < cmp->arity(); ++p2)
          {
            if (!isOpX<FAPP>(cmp->arg(p1)) && !isOpX<MPZ>(cmp->arg(p1)) &&
            !isOpX<MPQ>(cmp->arg(p1)))
              return indeterminate;
            if (cmp->arg(p1) == cmp->arg(p2))
              return false;
          }
        return true;
      }
      if (isOpX<AND>(cmp) || isOpX<OR>(cmp) || isOpX<XOR>(cmp))
      {
        bool doAnd = isOpX<AND>(cmp),
             doXor = isOpX<XOR>(cmp);
        tribool ret = evaluateCmpExpr(cmp->arg(0));
        for (int i = 1; i < cmp->arity(); ++i)
        {
          tribool subret = evaluateCmpExpr(cmp->arg(i));
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
        return !evaluateCmpExpr(cmp->left()) || evaluateCmpExpr(cmp->right());
      if (isOpX<ITE>(cmp))
        return evaluateCmpExpr(cmp->arg(0)) ?
          evaluateCmpExpr(cmp->arg(1)) : evaluateCmpExpr(cmp->arg(2));

      if (cmp->arity() > 2)
        return indeterminate;
      if (!isOpX<MPZ>(cmp->left()) || !isOpX<MPZ>(cmp->right()))
        return indeterminate;

      cpp_int li = lexical_cast<cpp_int>(cmp->left()),
              ri = lexical_cast<cpp_int>(cmp->right());
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

    ExprCoro getTravExpans(Expr con,
      const unordered_map<Expr,ExprUSet>& expmap)
    {
      return ExprCoro([&] (coroutine<Expr>::push_type& sink)
        {
          ExprVector fapps(expmap.size());
          filter(con, [] (Expr e) {
            return isOpX<FAPP>(e) && e->arity() == 1; }, fapps.begin());
          // Note that because of the internal ExprSet that dagVisit uses,
          //   we don't need to purge duplicates from `fapps`.
          ExprVector from;
          for (auto &f : fapps)
            if (f && expmap.count(f) != 0) from.push_back(f);
          ExprVector to(from.size());
          function<void(int)> perm = [&] (int pos)
          {
            if (pos == from.size())
              sink(replaceAll(con, from, to));
            else
              for (auto &expand : expmap.at(from[pos]))
              {
                to[pos] = expand;
                perm(pos + 1);
              }
          };
          perm(0);
        });
    }

    bool doesSatExpr(Expr con, const unordered_map<Expr,ExprUSet>& expmap,
      bool doAny, Expr origcon)
    {
      ExprCoro constcoro = getTravExpans(con, expmap);

      bool needsolver = false;
      ExprVector assertexps;
      if (doAny)
        assertexps.push_back(mk<FALSE>(m_efac));
      else
        assertexps.push_back(mk<TRUE>(m_efac));
      for (Expr &exp : constcoro)
      {
        tribool res = evaluateCmpExpr(exp);
        if (indeterminate(res))
        {
          res = evaluateCmpExpr(simplifyArithm(exp));
          if (indeterminate(res))
          {
            // We (maybe) don't want Z3 to evaluate variables as
            //   non-determinate integers.
            RW<function<Expr(Expr)>> rw(new function<Expr(Expr)>(
              [] (Expr e) -> Expr
            {
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
            exp = dagVisit(rw, exp);
            //m_smt_solver.assertExpr(exp);
            assertexps.push_back(exp);
            needsolver = true;
          }
          else if (!res)
            return false;
          else if (doAny)
            return true;
        }
        else if (!res)
          return false;
        else if (doAny)
          return true;
      }

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
          exit(1);
        }
        if (!res)
          return false;
        else if (doAny)
          return true;
      }

      return true;
    }

    bool doesSatConstraints(const ParseTree& pt)
    {
      unordered_map<Expr,ExprUSet> expmap;
      ExprUSet notselfdist, notselfeq;
      findExpansions(pt, expmap, notselfdist, notselfeq);

      for (auto &fullcon : constraints)
      {
        Expr con = fullcon->right();
        bool doAny = lexical_cast<string>(bind::fname(fullcon)->left()) ==
          "constraint_any";
        RW<function<Expr(Expr)>> fapprw(new function<Expr(Expr)>(
          [&notselfeq, &notselfdist, &expmap, &doAny, &pt] (Expr e) -> Expr
        {
          auto btoe = [&] (bool b) -> Expr
          {
            return b ? mk<TRUE>(e->efac()) : mk<FALSE>(e->efac());
          };

          if (isOpX<FAPP>(e))
          {
            string conname = lexical_cast<string>(bind::fname(e)->left());
            if (conname == "equal")
            {
              return btoe(notselfeq.count(e->right()) == 0);
            }
            else if (conname == "expands")
            {
              if (expmap.count(e->arg(1)) == 0)
                return mk<TRUE>(e->efac());
              int cnt = expmap.at(e->arg(1)).count(e->arg(2));
              if (!doAny)
              {
                // Make sure the ONLY expansion is the one given
                return btoe(cnt != 0 && expmap.at(e->arg(1)).size() == 1);
              }
              else if (cnt == 0)
                // Any expansion can be the one given
                return btoe(false);
              return btoe(true);
            }
            else if (conname == "present")
            {
              function<bool(const ParseTree&)> existhelper =
                [&] (const ParseTree& root) -> bool
              {
                if (root.data() == e->arg(1))
                  return true;
                for (auto& child : root.children())
                  if (existhelper(child))
                    return true;
                return false;
              };
              return btoe(existhelper(pt));
            }
            else
              return e;
          }
          else if (e->arity() == 1 && isOpX<NEQ>(e))
            return btoe(notselfdist.count(e->left()) == 0);
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
          exit(1);
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

        if (travpos.inqueue() && travpos.pos.limit != -1)
        {
          return gettrav(root, travpos.queueat(travpos.pos),
            localqvars, currnt, needdefer);
        }

        vector<ParseTree> cand;
        for (int i = 0; i < travpos.childrensize(); ++i)
        {
          cand.push_back(gettrav(root->arg(i), travpos.childat(i),
            localqvars, currnt, needdefer));
        }

        return ParseTree(root, cand);
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
          exit(1);
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

        vector<ParseTree> newexpr(root->arity());

        if (travpos.pos < 0 && !travpos.inqueue())
        {
          // First-time initialize
          if (travtype == TravParamType::ORDERED)
          {
            travpos = TravPos(0, root->arity());
            if (travdir == TravParamDirection::LTR)
              ++travpos.pos;
            else if (travdir == TravParamDirection::RTL)
              --travpos.pos;
          }
          else if (travtype == TravParamType::STRIPED)
          {
            if (travdir == TravParamDirection::LTR)
              travpos = TravPos(0, root->arity());
            else if (travdir == TravParamDirection::RTL)
              travpos = TravPos(0, root->arity());

            if (travdir == TravParamDirection::LTR)
              ++travpos.pos;
            else if (travdir == TravParamDirection::RTL)
              --travpos.pos;

            bool done = true;
            for (int i = 0; i < travpos.childrensize(); ++i)
            {
              newexpr[i] = newtrav(root->arg(i), travpos.childat(i),
                currdepth, qvars, currnt);
              done &= travpos.childat(i).isdone();
            }
            if (done)
              travpos.makedone();

            return ParseTree(root, newexpr);
          }
        }

        // Traversal

        int start, end;
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
        }

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

          for (int i = start; cond(i); i = nextpos(i))
          {
            if (i != travpos.pos)
            {
              assert(constpos.childat(i).pos >= 0);
              bool needdefer = false;
              if (travprio != TravParamPrio::DFS && i >= travpos.pos.min)
              {
                TravPos temppos;
                newexpr[i] = newtrav(root->arg(i), temppos,
                  currdepth, qvars, currnt);
              }
              else
                newexpr[i] = gettrav(root->arg(i), constpos.childat(i),
                  qvars, currnt, needdefer);
              if (needdefer)
              {
                if (constpos.childat(i).isdone())
                  travpos.childat(i) = TravPos();
                newexpr[i] = newtrav(root->arg(i), travpos.childat(i),
                  currdepth, qvars, currnt);
              }
            }
            else
            {
              assert(!constpos.childat(i).isdone());

              newexpr[i] = newtrav(root->arg(i), travpos.childat(i),
                currdepth, qvars, currnt);
              if (travpos.pos < end)
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

                  childpos->pos = CircularInt(nextpos(travpos.pos),
                      nextpos(travpos.pos), root->arity());
                  int startpos = nextpos(travpos.pos);
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
                    newtrav(root->arg(i), childpos->childat(i),
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
                newtrav(root->arg(travpos.pos),
                  travpos.childat(travpos.pos), currdepth, qvars, currnt);
                ++travpos.pos;
              }
            }
          }
        }
        else if (travtype == TravParamType::ORDERED)
        {
          int di = start;
          bool startreset = false;
          while (constpos.childat(di).isdone())
          {
            // Reset our position
            travpos.childat(di) = TravPos();
            newexpr[di] = newtrav(root->arg(di), travpos.childat(di),
              currdepth, qvars, currnt);
            if (di == start)
              startreset = true;

            assert(di != end);

            // Increment next position
            int nexti = nextpos(di);
            if (!constpos.childat(nexti).isdone())
            {
              newexpr[nexti] = newtrav(root->arg(nexti),
                travpos.childat(nexti), currdepth, qvars, currnt);
              break;
            }
            else
              di = nexti;
          }

          for (int i = di; cond(i); i = nextpos(i))
          {
            if (i != start)
            {
              if (constpos.childat(i).pos < 0)
                newtrav(root->arg(i), travpos.childat(i), currdepth, qvars,
                  currnt);
              bool needdefer = false;
              newexpr[i] = gettrav(root->arg(i), constpos.childat(i), qvars,
                currnt, needdefer);
              if (needdefer)
              {
                if (constpos.childat(i).isdone())
                  travpos.childat(i) = TravPos();
                newexpr[i] = newtrav(root->arg(i), travpos.childat(i),
                  currdepth, qvars, currnt);
              }
            }
          }

          if (!startreset && !constpos.childat(start).isdone())
            newexpr[start] = newtrav(root->arg(start), travpos.childat(start),
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
          unordered_map<std::pair<Expr, Expr>, int, pairhash> candnum;
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
            exit(1);
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
              aug_gram << "(declare-fun either (";
              for (int x = 1; x <= i; ++x)
              {
                aug_gram << sort_smt << " ";
              }
              aug_gram << ") " << sort_smt << ")\n";
            }

            // Special *_VARS variable
            aug_gram << "(declare-fun " << vars_name << " () " <<
              sort_smt << ")\n";
            // Generate *_prio declarations
            aug_gram << "(declare-fun prio (" <<
              sort_smt << " Real) " << sort_smt << ")\n";
            // Generate unary `equal` constraint declarations
            aug_gram << "(declare-fun equal (" << sort_smt << ") Bool)\n";
            // Generate binary `expands` constraint declarations
            aug_gram << "(declare-fun expands (" << sort_smt << " " <<
              sort_smt << ") Bool)\n";
            // Generate unary `present` constraint declarations
            aug_gram << "(declare-fun present (" << sort_smt << ") Bool)\n";
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
            exit(0);
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
            exit(0);
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
