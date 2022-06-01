#ifndef COROTRAV__HPP__
#define COROTRAV__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include <boost/coroutine2/coroutine.hpp>
#include <boost/optional.hpp>
#include <boost/optional/optional_io.hpp>

namespace ufo
{

using namespace boost::coroutines2;

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

  PTCoroCacheIter begin();

  PTCoroCacheIter end();
};

class PTCoroCacheIter
{
  int pos = 0;
  PTCoroCache *cache;

  inline void advancecoro()
  {
    assert(cache);
    while (cache->outcache.size() <= pos && cache->coro)
    {
      cache->outcache.push_back(cache->coro.get());
      cache->coro();
    }
    if (cache->outcache.size() <= pos)
      pos = -1;
  }

  public:

  PTCoroCacheIter(int _pos, PTCoroCache& _cache) : pos(_pos),
    cache(&_cache) {}
  PTCoroCacheIter(const PTCoroCacheIter& other) : pos(other.pos),
    cache(other.cache) {}
  PTCoroCacheIter(PTCoroCacheIter&& other) : pos(other.pos),
    cache(other.cache) {}

  PTCoroCacheIter& operator=(const PTCoroCacheIter& other)
  {
    pos = other.pos;
    cache = other.cache;
    return *this;
  }
  PTCoroCacheIter& operator=(PTCoroCacheIter&& other)
  {
    pos = other.pos;
    cache = other.cache;
    return *this;
  }

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

    return cache->outcache[pos];
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
    assert(cache);
    return std::move(PTCoroCacheIter(pos, *cache));
  }

  PTCoroCacheIter end()
  {
    assert(cache);
    return std::move(PTCoroCacheIter(-1, *cache));
  }
};

PTCoroCacheIter PTCoroCache::begin()
{
  return PTCoroCacheIter(0, *this);
}

PTCoroCacheIter PTCoroCache::end()
{
  return PTCoroCacheIter(-1, *this);
}

class tuplehash
{
  public:
  size_t operator()(const std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr>& tup) const
  {
    return std::hash<Expr>()(std::get<0>(tup)) *
      std::hash<int>()(std::get<1>(tup)) *
      std::hash<std::shared_ptr<ExprUSet>>()(std::get<2>(tup)) *
      std::hash<Expr>()(std::get<3>(tup));
  }
};

class CoroTrav : public Traversal
{
  private:

  // The main coroutine we use to traverse the grammar.
  std::unique_ptr<PTCoro> getNextCandTrav;

  // The sub-candidates previously generated with root == key
  unordered_map<std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr>,
    PTCoroCache,tuplehash> ptcorocache;

  Grammar &gram;
  bool grammodified = false;
  TravParams params;

  ParseTree nextcand; // Coroutines will destroy last cand once generated.
  ParseTree lastcand;

  int currmaxdepth = -1;

  // Helper function to convert from our format to Grammar's
  inline double grampriomapat(const pair<Expr,Expr> prod)
  {
    return gram.priomap.at(prod.first).at(prod.second).get_d();
  }

  void getNextCandTrav_fn(coroutine<ParseTree>::push_type &sink,
      Expr root = NULL, int currdepth = 0,
      std::shared_ptr<ExprUSet> qvars = NULL, Expr currnt = NULL)
  {
    //currnumcandcoros++;
    if (root == NULL)
      root = gram.root;

    /*outs() << "getNextCandTrav(" << root << ", " << currdepth << ", ";
    if (qvars != NULL)
      printvec(outs(), *qvars);
    else
      outs() << "NULL";
    outs() << ", " << currnt << ")" << endl;*/

    if (gram.isVar(root) || bind::isLit(root) || isOpX<FDECL>(root))
    {
      // Root is a symbolic variable; don't expand.
      sink(ParseTree(root));
      //currnumcandcoros--;
      return;
    }
    else if (gram.isNt(root))
    {
      if (root != currnt && !gram.pathExists(root, currnt))
      {
        currdepth = 0;
        currnt = root;
      }
      vector<int> order;

      auto &prods = gram.prods.at(root);
      if (prods.size() == 0)
      {
        CFGUtils::noNtDefError(root, gram.root);
        sink(NULL); // Unreachable
        return;
      }

      if (params.order == TPOrder::FOR)
        for (int i = 0; i < prods.size(); ++i)
        {
          if (!gram.isRecursive(prods[i], root) ||
          currdepth < currmaxdepth)
            order.push_back(i);
        }
      else if (params.order == TPOrder::REV)
        for (int i = prods.size() - 1; i >= 0; --i)
        {
          if (!gram.isRecursive(prods[i], root) ||
          currdepth < currmaxdepth)
            order.push_back(i);
        }
      else if (params.order == TPOrder::RND)
      {
        set<int> done;
        while (done.size() < prods.size())
        {
          // Offset by 1 because arg(0) is the fdecl.
          int randnum = (rand() % (prods.size()));

          if (!done.insert(randnum).second)
            continue;

          // Don't traverse past maximum depth
          if (!gram.isRecursive(prods[randnum], root) ||
          currdepth < currmaxdepth)
            order.push_back(randnum);
        }
      }

      if (order.size() == 0)
      {
        sink(NULL);
        return;
      }

      // First: Production, Second: Coroutine
      list<std::pair<std::pair<NT,Expr>,PTCoroCacheIter>> coros;
      for (int i : order)
      {
        Expr prod = prods[i];
        int newdepth;
        if (gram.isRecursive(prod, root))
          newdepth = currdepth + 1;
        else
          newdepth = currdepth;

        coros.push_back(std::move(make_pair(make_pair(root, prod),
          getCandCoro(prod, newdepth, qvars, currnt))));
        if (!*coros.back().second)
          coros.pop_back();
        else if (params.type == TPType::STRIPED)
        {
          sink(ParseTree(root, vector<ParseTree>{*coros.back().second}, true));
          ++coros.back().second;
          if (!coros.back().second)
            coros.pop_back();
        }
      }

      // Without in-coro priorities
      /*bool notdone = true;
      while (notdone)
      {
        notdone = false;
        for (auto &coro : coros)
        {
          if (!coro.second)
            continue;
          notdone = true;
          sink(*coro.second);
          ++coro.second;
        }
      }
      return;*/

      // With in-coro priorities
      auto lastbest = coros.begin();

      // Key: <Either Expr, Non-terminal>,
      // Value: number of cands generated with Production
      unordered_map<std::pair<NT, Expr>, int> candnum;
      int totalcandnum = 0;

      // prod has same format as Key of candnum
      auto shoulddefer = [&] (const std::pair<NT,Expr>& prod) -> bool
      {
        if (candnum[prod] == 0 ||
          grampriomapat(prod) == 1)
          return false;
        return candnum[prod] > (int)(grampriomapat(prod)*totalcandnum);
      };

      for (auto &kv : coros)
      {
        candnum[kv.first] = 0;
      }

      while (coros.size() != 0)
      {
        bool didsink = false;

        if (params.type == TPType::ORDERED)
        {
          auto itr = coros.begin();
          if (coros.size() != 0 && itr != coros.end())
          {
            while (itr != coros.end() && shoulddefer(itr->first))
              ++itr;

            if (itr != coros.end())
            {
              sink(ParseTree(root, vector<ParseTree>{*itr->second}, true));
              candnum[itr->first]++;
              ++totalcandnum;
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
        else if (params.type == TPType::STRIPED)
        {
          for (auto itr = coros.begin(); itr != coros.end();)
          {
            if (shoulddefer(itr->first))
            {
              ++itr;
              continue;
            }

            sink(ParseTree(root, vector<ParseTree>{*itr->second}, true));
            didsink = true;
            candnum[itr->first]++;
            ++totalcandnum;
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
            if (grampriomapat(itr->first) > grampriomapat(bestcoro->first))
            {
              bestcoro = itr;
              setbestcoro = true;
            }
          }

          if (!setbestcoro)
          {
            auto itr = lastbest;
            if (params.type == TPType::STRIPED)
              ++itr;
            for (; itr != coros.end(); ++itr)
            {
              if (grampriomapat(itr->first) >= grampriomapat(bestcoro->first))
              {
                bestcoro = itr;
                setbestcoro = true;
                break;
              }
            }
          }

          sink(ParseTree(root, vector<ParseTree>{*bestcoro->second}, true));
          candnum[bestcoro->first]++;
          ++totalcandnum;
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
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL &&
        qvars->find(root->first()) != qvars->end())
      {
          // Root is a variable for a surrounding quantifier
          sink(ParseTree(root));
          //currnumcandcoros--;
          return;
      }
      else if (root->arity() == 1)
      {
        CFGUtils::noNtDefError(root, gram.root);
        sink(NULL); // Unreachable
        return;
      }
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
      if (params.type == TPType::ORDERED)
      {
        argcoros.push_back(boost::none);
        expanded_args.push_back(NULL);
      }
      else
      {
        argcoros.push_back(getCandCoro(*itr, currdepth, localqvars, currnt));
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
    if (ptcorocache.count(tup) == 0)
    {
      ptcorocache.emplace(tup, std::move(PTCoroCache(std::move(
        PTCoro(std::bind(&CoroTrav::getNextCandTrav_fn, this,
        std::placeholders::_1, root, currdepth, qvars, currnt))))));
      didemplace = true;
    }
    return ptcorocache.at(tup).begin();
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

    // To reverse ('rtl'), we just invert cand and root->arg(i)
    /*auto sink = [this, &realsink] (ParseTree pt)
    {
      if (params.dir == TPDir::RTL &&
      !isOpX<FAPP>(pt.data()) && pt.data()->arity() != 0)
        std::reverse(pt.children().begin(), pt.children().end());
      realsink(std::move(pt));
    };
    function<Expr(int)> rootarg;
    if (params.dir == TPDir::LTR)
      rootarg = [&] (int i) { return root->arg(i); };
    else if (params.dir == TPDir::RTL)
      rootarg = [&] (int i) { return root->arg(root->arity()-1-i); };
    */
    function<int(int)> dindex;
    if (params.dir == TPDir::LTR)
      dindex = [&] (int i) { return i; };
    else if (params.dir == TPDir::RTL)
      dindex = [&] (int i) { return root->arity()-1-i; };
    auto rootarg = [&] (int i) { return root->arg(dindex(i)); };

    if (params.type == TPType::STRIPED ||
    stuck.size() == cand.size())
    {
      //sink(m_efac.mkNary(root->op(), cand));
      bool foundnull = false;
      for (const auto& p : cand)
        if (!p)
        {
          sink(NULL);
          foundnull = true;
        }
      if (!foundnull) sink(ParseTree(root, cand, false));
    }

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
            ParseTree ret = meth.get();
            if (ret)
              sink(ret);
            meth();
            methcoroavail = true;
          }
        }
      }
      methcoros.clear();
    };

    if (params.type == TPType::STRIPED)
    {
      vector<int> free;
      int min_i = 0, max_i = coros.size();
      if (stuck.size() != 0)
        min_i = *(--stuck.end()) + 1;
      for (int i = min_i; i < max_i; ++i)
        free.push_back(i);

      if (params.dir == TPDir::RND)
        random_shuffle(free.begin(), free.end());

      auto inloopfn = [&] (int pos) -> bool {
        if (!*coros[dindex(pos)])
          return false;

        vector<ParseTree> newcand = cand;
        newcand[dindex(pos)] = coros[dindex(pos)]->get();
        (*coros[dindex(pos)])();
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
        {
          //sink(m_efac.mkNary(root->op(), newcand));
          for (const auto& p : newcand)
            if (!p)
            {
              sink(NULL);
              return true;
            }
          sink(ParseTree(root, newcand, false));
          int b = 0;
        }
        else
        {
          vector<optional<PTCoroCacheIter>> newcoros(coros.size());
          for (int i = 0; i < coros.size(); ++i)
          {
            if (newstuck.find(i) == newstuck.end())
            {
              newcoros[dindex(i)] = std::move(getCandCoro(rootarg(i),
                  currdepth, qvars, currnt));
              newcand[dindex(i)] = newcoros[dindex(i)]->get();
              (*newcoros[dindex(i)])();
            }
          }

          methcoros.push_back(getTravCoro(std::move(newcoros),
           std::move(newcand),std::move(newstuck),root,currdepth,qvars,currnt));
          sink(methcoros.back().get());
          methcoros.back()();
        }

        return true;
      };

      if (params.prio != TPPrio::DFS)
      {
        bool coroavail = true;
        while (coroavail)
        {
          coroavail = false;
          for (int i : free)
            coroavail |= inloopfn(i);
          if (params.prio == TPPrio::BFS)
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
    else if (params.type == TPType::ORDERED)
    {
      vector<int> free;
      for (int i = 0; i < cand.size(); ++i)
        if (stuck.find(i) == stuck.end())
          free.push_back(i);

      int nextstuck;
      nextstuck = free.back();
      if (params.dir == TPDir::RND)
        nextstuck = free[rand() % free.size()];

      PTCoroCacheIter nextcoro = getCandCoro(rootarg(nextstuck),
        currdepth, qvars, currnt);

      set<int> newstuck = stuck;
      newstuck.insert(nextstuck);

      for (ParseTree exp : nextcoro)
      {
        cand[dindex(nextstuck)] = exp;

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
        {
          //sink(m_efac.mkNary(root->op(), cand));
          bool foundnull = false;
          for (const auto& p : cand)
            if (!p)
            {
              sink(NULL);
              foundnull = true;
            }
          if (!foundnull) sink(ParseTree(root, cand, false));
        }
        else
        {
          PTCoro newmeth = getTravCoro(std::move(newcoros), cand,
            newstuck, root, currdepth, qvars, currnt);
          for (ParseTree exp : newmeth)
            if (exp)
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

  void handleGramMod()
  {
    assert(0 && "Coroutine traversal does not support modifying Grammar mid-traversal!");
    grammodified = false;
  }

  void onGramMod(ModClass cl, ModType ty)
  {
    if (cl == ModClass::CONSTRAINT && ty == ModType::ADD)
      return;
    grammodified = true;
    lastcand = NULL;
    nextcand = NULL;
  }
  std::shared_ptr<ModListener> mlp;

  void invalidateCache()
  {
    // Invalidate NTs that are recursive and their "parents"
    unordered_set<NT> recursiveNts, needInvalidate;
    for (const NT& nt : gram.nts)
      if (gram.pathExists(nt, nt))
        recursiveNts.insert(nt);
    for (const NT& nt : gram.nts)
    {
      if (recursiveNts.count(nt) != 0)
        needInvalidate.insert(nt);
      else
        for (const NT& recNt : recursiveNts)
          if (gram.pathExists(nt, recNt))
            needInvalidate.insert(nt);
    }

    for (auto itr = ptcorocache.begin(); itr != ptcorocache.end();)
    {
      const Expr& root = get<0>(itr->first);
      bool invalidate = false;
      if (gram.isVar(root) || bind::isLit(root))
      {
        // No need to invalidate literals/variables
        invalidate = false;
      }
      else if (gram.isNt(root))
        invalidate = needInvalidate.count(root) != 0;
      else // A production
      {
        ExprVector prodnts;
        filter(root, [&](Expr e){return gram.isNt(e);}, inserter(prodnts, prodnts.begin()));
        for (const Expr& nt : prodnts)
          if (needInvalidate.count(nt) != 0)
          {
            invalidate = true;
            break;
          }
      }

      if (invalidate)
        itr = ptcorocache.erase(itr);
      else
        ++itr;
    }
  }

  void init()
  {
    std::shared_ptr<ExprUSet> qvars = NULL;
    int currdepth = 0;
    Expr currnt = NULL;
    // This will start the coroutine, running until first yield
    getNextCandTrav.reset(new PTCoro(
          std::bind(&CoroTrav::getNextCandTrav_fn, this,
          std::placeholders::_1, gram.root, currdepth, qvars, currnt)));
    nextcand = getNextCandTrav->get();
    (*getNextCandTrav)();
    nextcand.fixchildren();
  }

  public:

  CoroTrav(Grammar &_gram,const TravParams &tp) : gram(_gram), params(tp)
  {
    if (params.iterdeepen)
      currmaxdepth = 0;
    else
    {
      assert(params.maxrecdepth >= 0);
      currmaxdepth = params.maxrecdepth;
    }

    mlp.reset(new ModListener(
      [&] (ModClass cl, ModType ty) { return onGramMod(cl, ty); }));
    bool ret = gram.addModListener(mlp);
    assert(ret);
    init();
  }

  virtual ~CoroTrav()
  {
    bool ret = gram.delModListener(mlp);
    assert(ret);
  }

  virtual bool IsDone()
  {
    return IsDepthDone() && currmaxdepth == params.maxrecdepth;
  }

  virtual bool IsDepthDone()
  {
    if (grammodified) handleGramMod();
    return !nextcand && !bool(*getNextCandTrav);
  }

  virtual int GetCurrDepth()
  {
    return currmaxdepth;
  }

  virtual ParseTree GetCurrCand()
  {
    return lastcand;
  }

  virtual ParseTree Increment()
  {
    if (grammodified) handleGramMod();
    if (IsDone())
    {
      lastcand = NULL;
      return NULL;
    }
    if (IsDepthDone())
    {
      invalidateCache();
      currmaxdepth++;
      init();
    }
    lastcand = nextcand;
    if (!*getNextCandTrav)
    {
      nextcand = NULL;
      return lastcand;
    }
    nextcand = getNextCandTrav->get();
    (*getNextCandTrav)();
    nextcand.fixchildren();
    return lastcand;
  }
};

}
#endif
