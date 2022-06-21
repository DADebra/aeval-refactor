#ifndef NEWTRAV__HPP__
#define NEWTRAV__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include "gram/TupleHash.hpp"

#include "gram/TravPos.hpp"

// Uncomment to always disable path collision checking
//#define DO_PATH_COLL_CHECK 0

// Else, check for collisions if debug builds are enabled
// (the checking relies on 'assert', so won't work if NDEBUG is defined)
#ifndef DO_PATH_COLL_CHECK
#ifndef NDEBUG
#define DO_PATH_COLL_CHECK 1
#else
#define DO_PATH_COLL_CHECK 0
#endif // #ifndef NDEBUG
#endif // #ifndef DO_PATH_COLL_CHECK

namespace ufo
{

#if DO_PATH_COLL_CHECK == 1
typedef std::pair<size_t,string> Path;
#else
typedef size_t Path;
#endif

class NewTrav : public Traversal
{
  private:

  // The hash of the root path
  const static Path rootpath, nullpath;

  enum PathClass { C = 1, Q = 2 };

  CFGUtils cfgutils;

  Grammar &gram;
  bool grammodified = false;
  TravParams gparams;
  NTParamMap ntparams;
  TravPos rootpos;
  function<bool(const Expr&, const Expr&)> shoulddefer;

  ExprFactory& efac;

  UniqVarMap uniqvars; // Per-candidate
  unordered_map<size_t, mpz_class> uniqvarnums; // Nicer unique numbers
  mpz_class lastuniqvarnum = -1;

  ParseTree lastcand; // Not strictly necessary, but for efficiency.

  int currmaxdepth = -1;

  // I'm not sure why, but using the Path as the key here won't work
  unordered_map<const TravPos*,ParseTree> gettravCache;
  unordered_map<std::tuple<Expr,int,Expr,size_t>,ParseTree> getfirstCache;

#if DO_PATH_COLL_CHECK == 1
  unordered_map<size_t,string> pathCollisionCheck;
#endif

  // Extend the hash of the current path 'currhash' by position 'index'
  //   and class (queue or child) 'class'.
  // This number is used to uniquely identify where we are
  //   in the recursive invocations of 'newtrav'.
  // Note that this is the TRAVERSAL path (note the inclusion of the queue)
  //   and not the GRAMMAR path (which would mean that queue items have the
  //   same path).
  inline Path np(Path currhash, PathClass pclass, unsigned index)
  {
#if DO_PATH_COLL_CHECK == 1
    hash_combine(currhash.first, pclass);
    hash_combine(currhash.first, index + 1);
#else
    hash_combine(currhash, pclass);
    hash_combine(currhash, index + 1);
#endif

#if DO_PATH_COLL_CHECK == 1
    currhash.second += pclass == C ? "C" : "Q";
    currhash.second += to_string(index);
    auto itr = pathCollisionCheck.find(currhash.first);
    if (itr != pathCollisionCheck.end())
      assert(itr->second == currhash.second);
    else
      pathCollisionCheck.emplace(currhash.first, currhash.second);
#endif
    return currhash;
  }

  inline void ptshoulddefer(const ParseTree& pt, bool& needdefer)
  {
    pt.foreachPt([&] (const Expr& nt, const ParseTree& expand)
    { needdefer |= shoulddefer(nt, expand.data()); });
  }

  ParseTree gettrav(const Expr& root, const TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars, Expr currnt, Path path, const TravParams& oldparams,
    bool& needdefer, bool getfirst)
  {
    size_t phash;
#if DO_PATH_COLL_CHECK == 1
    phash = path.first;
#else
    phash = path;
#endif

    const TravParams& params = ntparams.count(root) != 0 ? ntparams[root] : oldparams;
    const TravParams& nextparams = params.propagate ? params : oldparams;

    if (!getfirst && travpos.isnull())
      return NULL;

    if (gram.isVar(root) || bind::isLit(root) || gram.isConst(root) || isOpX<FDECL>(root))
      // Root is a symbolic variable
      return ParseTree(root);
    if (gram.isUniqueVar(root))
    {
      auto itr = uniqvarnums.find(phash);
      assert(itr != uniqvarnums.end());
      Expr uniqvar = mk<FAPP>(CFGUtils::uniqueVarDecl(typeOf(root)),
        mkTerm(itr->second, efac));
      return ParseTree(root, uniqvar, false);
    }

    bool isNt = gram.isNt(root);

    if (!isNt && isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
        // Root is a closed (quantified) variable
        return ParseTree(root);
      else if (root->arity() == 1)
      {
        // Should never happen
        // There's no definition, we're expanding an empty *_VARS
        CFGUtils::noNtDefError(root, gram.root);
        return NULL;
      }
    }

    std::tuple<Expr,int,Expr,size_t> firstkey;
    if (!getfirst)
    {
      auto itr = gettravCache.find(&travpos);
      if (itr != gettravCache.end())
      {
        if (itr->second)
          ptshoulddefer(itr->second, needdefer);
        return itr->second;
      }
    }
    else
    {
      // Will be used when we return
      firstkey = std::move(make_tuple(root, currdepth, currnt, phash));
      auto itr = getfirstCache.find(firstkey);
      if (itr != getfirstCache.end())
      {
        if (itr->second)
          ptshoulddefer(itr->second, needdefer);
        return itr->second;
      }
    }

    CircularInt pos = travpos;
    pos.min = 0;
    const TravPos *nextpos = &travpos;

    if (isNt)
    {
      if (root != currnt && !gram.pathExists(root, currnt))
      {
        currdepth = 0;
        currnt = root;
      }
      const auto& prods = gram.prods.at(root);
      if (getfirst)
      {
        pos.limit = prods.size();
        if (params.order == TPOrder::FOR)
          pos = 0;
        else if (params.order == TPOrder::REV)
          pos = prods.size() - 1;
        int startpos = pos;
        while (gram.isRecursive(prods[pos], root) &&
          currdepth == currmaxdepth)
        {
          if (params.order == TPOrder::FOR) ++pos;
          else if (params.order == TPOrder::REV) --pos;
          if (pos == startpos)
          {
            getfirstCache[firstkey] = NULL;
            return NULL;
          }
        }
      }
      else
        nextpos = &travpos.childat(pos);

      int newdepth;
      if (gram.isRecursive(prods[pos], root))
        newdepth = currdepth + 1;
      else
        newdepth = currdepth;

      int startpos = pos;
      ParseTree ret = NULL;
      while (!ret)
      {
        ret = std::move(gettrav(prods[pos], *nextpos, newdepth,
          qvars, currnt, np(path,C,pos), nextparams, needdefer, getfirst));
        if (!getfirst) assert(ret);
        if (!ret)
        {
          if (params.order == TPOrder::FOR) ++pos;
          else if (params.order == TPOrder::REV) --pos;
          if (pos == startpos)
          {
            getfirstCache[firstkey] = NULL;
            return NULL;
          }
          if (gram.isRecursive(prods[pos], root))
            newdepth = currdepth + 1;
          else
            newdepth = currdepth;
        }
      }
      assert(ret);
      needdefer = needdefer || shoulddefer(root, prods[pos]);
      ret = ParseTree(root, std::move(ret), true);
      if (getfirst)
        getfirstCache[firstkey] = ret;
      else
        gettravCache[&travpos] = ret;
      return std::move(ret);
    }

    // Root is a Z3 function (e.g. (and ...))
    std::shared_ptr<ExprUSet> localqvars(new ExprUSet());

    if (qvars != NULL)
      for (auto& var : *qvars)
        localqvars->insert(var);

    if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      // Add quantifier variables to qvars
      for (int i = 0; i < root->arity() - 1; ++i)
        localqvars->insert(root->arg(i));

    vector<ParseTree> newexpr(root->arity());

    // To reverse ('rtl'), we just invert newexpr and root->arg(i)
    function<int(int)> dind;
    if (params.dir == TPDir::LTR)
      dind = [&] (int i) { return i; };
    else if (params.dir == TPDir::RTL)
      dind = [&] (int i) { return root->arity()-1-i; };

    if (params.type == TPType::ORDERED)
    {
      for (int i = 0; i < root->arity(); ++i)
      {
        if (!getfirst)
          nextpos = &travpos.childat(dind(i));
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), *nextpos, currdepth,
          localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, getfirst);
        if (!newexpr[dind(i)])
        {
          if (getfirst)
            getfirstCache[firstkey] = NULL;
          else
            gettravCache[&travpos] = NULL;
          return NULL;
        }
      }
      ParseTree ret(root, std::move(newexpr), false);

      if (getfirst)
        getfirstCache[firstkey] = ret;
      else
        gettravCache[&travpos] = ret;
      return std::move(ret);
    }

    if (travpos.inqueue())
    {
      assert(!getfirst);

      ParseTree ret(std::move(gettrav(root, travpos.queueat(pos), currdepth,
        localqvars, currnt, np(path,Q,pos), oldparams, needdefer, getfirst)));
      gettravCache[&travpos] = ret;
      return std::move(ret);
    }

    if (getfirst)
      pos = -1;

    for (int i = 0; i < root->arity(); ++i)
    {
      if (i >= travpos.min() && i != pos)
      {
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), travpos, currdepth,
          localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, true);
        if (!newexpr[dind(i)])
        {
          if (getfirst)
            getfirstCache[firstkey] = NULL;
          else
            gettravCache[&travpos] = NULL;
          return NULL;
        }
      }
      else
      {
        if (!getfirst)
          nextpos = &travpos.childat(dind(i));
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), *nextpos, currdepth,
          localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, getfirst);
        if (!newexpr[dind(i)])
        {
          if (getfirst)
            getfirstCache[firstkey] = NULL;
          else
            gettravCache[&travpos] = NULL;
          return NULL;
        }
      }
    }

    ParseTree ret(root, std::move(newexpr), false);

    if (getfirst)
      getfirstCache[firstkey] = ret;
    else
      gettravCache[&travpos] = ret;
    return std::move(ret);
  }

  ParseTree newtrav(const Expr& root, TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars, Expr currnt, Path path,
    const TravParams& oldparams, Path mu, bool ro)
  {
    // mu: Only increment positions below this path
    // ro: Read-only, don't increment positions

    const TravParams& params = ntparams.count(root) != 0 ? ntparams[root] : oldparams;
    const TravParams& nextparams = params.propagate ? params : oldparams;

    if (path == mu)
      ro = false;

    if (!ro)
    {
      assert(("Cannot increment TravPos which is done!" && !travpos.isdone()));
      assert(("Cannot increment TravPos which is r/o!" && !travpos.readonly()));
    }

    if (ro && travpos.isnull())
      return NULL;

    gettravCache.erase(&travpos);

    // Some operations should not cause copy-up; use constpos for these.
    const TravPos &constpos = travpos;

    if (gram.isVar(root) || bind::isLit(root) || gram.isConst(root) || isOpX<FDECL>(root))
    {
      // Root is a symbolic variable
      if (!ro) travpos.makedone();
      return ParseTree(root);
    }
    else if (gram.isUniqueVar(root))
    {
      size_t phash;
#if DO_PATH_COLL_CHECK == 1
      phash = path.first;
#else
      phash = path;
#endif
      auto itr = uniqvarnums.find(phash);
      if (itr == uniqvarnums.end())
        itr = uniqvarnums.emplace(phash, ++lastuniqvarnum).first;
      Expr uniqvar = mk<FAPP>(CFGUtils::uniqueVarDecl(typeOf(root)),
        mkTerm(itr->second, efac));
      if (!ro) travpos.makedone();
      return ParseTree(root, uniqvar, false);
    }
    else if (gram.isNt(root))
    {
      if (root != currnt && !gram.pathExists(root, currnt))
      {
        currdepth = 0;
        currnt = root;
      }
      const auto &prods = gram.prods.at(root);
      if (prods.size() == 0)
      {
        CFGUtils::noNtDefError(root, gram.root);
        return NULL; // Unreachable
      }

      if (travpos.isnew())
      {
        assert(!ro);
        // First-time initialize
        travpos = TravPos(0, prods.size());
        if (params.type != TPType::STRIPED)
        {
          if (params.order == TPOrder::FOR)
            travpos.nextpos();
          else if (params.order == TPOrder::REV)
            travpos.prevpos();
        }
      }

      if (!ro && params.type == TPType::STRIPED)
      {
        if (params.order == TPOrder::FOR)
          travpos.nextpos();
        else if (params.order == TPOrder::REV)
          travpos.prevpos();
      }

      /*while (constpos.childat(checkpos).isdone() ||
      (gram.isRecursive(prods[checkpos], root) &&
       currdepth == currmaxdepth))
      {
        if (params.order == TPOrder::FOR)
          ++checkpos;
        else if (params.order == TPOrder::REV)
          --checkpos;

        assert(checkpos != startpos);
      }

      startpos = checkpos;*/
      bool checkprio = true;
      ParseTree ret(NULL);
      int newdepth;
      int startpos = travpos.pos();
      for (;;)
      {
        if (!ro)
        {
          while (constpos.childat(travpos.pos()).isdone() ||
           (checkprio && shoulddefer(root, prods[travpos.pos()])) ||
           (gram.isRecursive(prods[travpos.pos()], root) &&
           currdepth == currmaxdepth))
          {
            if (constpos.childat(travpos.pos()).isdone())
              travpos.childpop();

            if (params.order == TPOrder::FOR)
              travpos.nextpos();
            else if (params.order == TPOrder::REV)
              travpos.prevpos();

            if (travpos.pos() == startpos)
            {
              if (checkprio)
                // All productions must be deferred; pick first one
                checkprio = false;
              else
              {
                travpos.makenull();
                return NULL;
              }
            }
          }
        }

        if (gram.isRecursive(prods[travpos.pos()], root))
          newdepth = currdepth + 1;
        else
          newdepth = currdepth;

        assert(newdepth <= currmaxdepth);

        ret = ParseTree(root, std::move(newtrav(prods[travpos.pos()],
          travpos.childat(travpos.pos()), newdepth, qvars, currnt,
          np(path,C,travpos.pos()), nextparams, mu, ro)), true);

        if (!ret.children()[0])
          // The either we picked is done at that recursive depth. Pick another.
          continue;
        break;
      }

      if (!ro)
      {
        // Check to see if we're done.
        startpos = travpos.pos();
        CircularInt checkpos = travpos;
        bool alldone = true, // Completely done
             recdone = true; // Just done at this recursion depth
        do
        {
          bool isrec = gram.isRecursive(prods[checkpos], root) &&
            currdepth == currmaxdepth;
          bool isdone = constpos.childat(checkpos).isdone();

          alldone &= isdone;
          recdone &= (isrec || isdone);

          if (params.order == TPOrder::FOR)
            ++checkpos;
          else if (params.order == TPOrder::REV)
            --checkpos;
        } while (checkpos != startpos);

        if (alldone || recdone)
          travpos.makedone();
      }

      assert(ret);
      bool unused = false;
      ParseTree getpt(std::move(gettrav(root, constpos, currdepth,
        qvars, currnt, path, oldparams, unused, false)));
      assert(getpt == ret);
      return std::move(ret);
    }
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
      {
        // Root is a closed (quantified) variable
        if (!ro) travpos.makedone();
        return ParseTree(root);
      }
      else if (root->arity() == 1)
      {
        // There's no definition, we're expanding an empty *_VARS
        CFGUtils::noNtDefError(root, gram.root);
        return NULL;
      }
    }

    // Root is a Z3 function (e.g. (and ...))
    std::shared_ptr<ExprUSet> localqvars(new ExprUSet());
    vector<ParseTree> newexpr(root->arity());

    if (qvars != NULL)
      for (auto& var : *qvars)
        localqvars->insert(var);

    if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      // Add quantifier variables to qvars
      for (int i = 0; i < root->arity() - 1; ++i)
        localqvars->insert(root->arg(i));

    // To reverse ('rtl'), we just invert newexpr and root->arg(i)
    function<ParseTree&(int)> newexprat;
    function<Expr(int)> rootarg;
    function<TravPos&(int)> travposchildat;
    function<const TravPos&(int)> constposchildat;
    function<int(int)> dind;
    if (params.dir == TPDir::LTR)
      dind = [&] (int i) { return i; };
    else if (params.dir == TPDir::RTL)
      dind = [&] (int i) { return root->arity()-1-i; };

    newexprat = [&] (int i) -> ParseTree& { return newexpr[dind(i)]; };
    rootarg = [&] (int i) { return root->arg(dind(i)); };
    travposchildat = [&] (int i) -> TravPos&
      { return travpos.childat(dind(i)); };
    constposchildat = [&] (int i) -> const TravPos& { return constpos.childat(dind(i)); };

    if (travpos.isnew())
    {
      // First-time initialize
      assert(!ro);
      travpos = TravPos(0, root->arity());

      if (params.type == TPType::STRIPED)
      {
        bool done = true;
        bool foundnull = false;
        for (int i = 0; i < travpos.childlimit(); ++i)
        {
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);
          if (!newexprat(i))
            foundnull = true;
          bool idone = constposchildat(i).isdone();
          if (idone && i == travpos.pos())
            travpos.nextpos();
          done &= idone;
        }
        if (done)
          travpos.makedone();
        else if (params.prio == TPPrio::DFS)
          travpos.nextpos();

        if (foundnull)
        {
          travpos.makenull();
          return NULL;
        }

        return ParseTree(root, std::move(newexpr), false);
      }
      else
        travpos.nextpos();
    }

    // Traversal

    if (params.type == TPType::STRIPED)
    {
      if (!ro && !travpos.inqueue())
      {
        if (params.prio != TPPrio::DFS)
        {
          travpos.nextpos();
          if (travpos.pos() == travpos.min() &&
          params.prio == TPPrio::BFS &&
          constpos.queuelimit() != 0)
            travpos.makeinqueue();
          else
          {
            int startpos = travpos.pos();
            while (constposchildat(travpos.pos()).isdone())
            {
              travpos.nextpos();
              if (travpos.pos() == startpos ||
              (params.prio == TPPrio::BFS &&
              travpos.pos() == travpos.min()))
              {
                if (constpos.queuelimit() != 0)
                  travpos.makeinqueue();
                break;
              }
            }
          }
        }
        else if (constposchildat(travpos.pos()).isdone())
        {
          travpos.nextpos();
          if (travpos.pos() == travpos.min())
          {
            assert(constpos.queuelimit() != 0);
            travpos.makeinqueue();
          }
        }
      }
      else if (!ro)
      {
        travpos.nextpos();

        bool done = true;
        for (unsigned int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
          done &= constpos.queueat(i).isdone();
        if (done)
        {
          for (int i = travpos.childmin(); i < travpos.childlimit(); ++i)
            done &= constposchildat(i).isdone();
          if (done)
          {
            travpos.makenull();
            return NULL;
          }
          travpos.makenotinqueue();
          while (constposchildat(travpos.pos()).isdone())
          {
            travpos.nextpos();
            assert(travpos.pos() != travpos.min());
          }
        }

        if (travpos.inqueue())
          while (constpos.queueat(travpos.pos()).isdone())
            travpos.queuepop();
      }


      if (travpos.inqueue())
      {
        ParseTree ret(NULL);
        ret = std::move(newtrav(root, travpos.queueat(travpos.pos()),
          currdepth, localqvars, currnt, np(path,Q,travpos.pos()), oldparams, mu, ro));
        if (!ret)
          return std::move(newtrav(root, travpos, currdepth,
            qvars, currnt, path, oldparams, mu, ro));

        if (!ro)
        {
          bool done = true;
          for (unsigned int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
            done &= constpos.queueat(i).isdone();
          if (done)
          {
            if (params.prio != TPPrio::BFS)
              travpos.makedone();
            else
            {
              for (int i = travpos.childmin(); i < travpos.childlimit(); ++i)
                done &= constposchildat(i).isdone();
              if (done)
                travpos.makedone();
            }
          }
        }

        assert(ret);
        bool unused = false;
        ParseTree getpt = std::move(gettrav(root,
          constpos.queueat(travpos.pos()), currdepth, localqvars, currnt,
          np(path,Q,travpos.pos()), oldparams, unused, false));
        assert(getpt == ret);
        return std::move(ret);
      }

      for (int i = 0; i < travpos.childlimit(); ++i)
      {
        if (i != travpos.pos())
        {
          assert(!constposchildat(i).isnew());
          bool needdefer = false;
          if (i >= travpos.childmin())
          {
            newexprat(i) = gettrav(rootarg(i), travpos, currdepth,
              localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, true);
          }
          else
            newexprat(i) = gettrav(rootarg(i), constposchildat(i), currdepth,
              localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, false);
          /*if (needdefer)
          {
            if (constposchildat(i).isdone())
              travposchildat(i) = TravPos();
            newexprat(i) = newtrav(rootarg(i), travposchildat(i),
              currdepth, localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);
          }*/
        }
        else
        {
          if (!ro) assert(!constposchildat(i).isdone());

          newexprat(i) = newtrav(rootarg(i), travposchildat(i), currdepth,
            localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);

          if (!ro && travpos.pos() < travpos.childlimit() - 1)
          {
            TravPos *childpos = new TravPos(travpos, false);
            Path childpath = np(path,Q,travpos.queuelimit());

            childpos->setmin(travpos.pos() + 1);

            if (params.prio == TPPrio::DFS)
              childpos->nextpos();

            for (int i = travpos.childmin(); i < travpos.childlimit(); ++i)
            {
              if (i == travpos.pos())
                continue;
              childpos->childat(dind(i)) = TravPos();
              newtrav(rootarg(i), childpos->childat(dind(i)), currdepth,
                localqvars, currnt, np(childpath,C,dind(i)),nextparams,mu,ro);
            }

            bool done = true;
            const TravPos *constchild = (const TravPos*)childpos;
            for (int i= childpos->childmin(); i < childpos->childlimit(); ++i)
              if (!constchild->childat(dind(i)).isdone())
              {
                done = false;
                break;
              }

            if (!done)
              travpos.queuepush_back(childpos);
          }
        }
      }

      if (!ro)
      {
        bool done = true;
        for (int i = constpos.childmin(); i < constpos.childlimit(); ++i)
          if (!constposchildat(i).isdone())
          {
            done = false;
            break;
          }
        if (done)
          for (unsigned int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
            if (!constpos.queueat(i).isdone())
            {
              done = false;
              break;
            }

        if (done)
          travpos.makedone();
      }

      /*if (params.dir == TPDir::LTR)
        ++travpos.pos;
      else if (params.dir == TPDir::RTL)
        --travpos.pos;*/
      /*int startpos = travpos.pos;
      while (travpos.children[travpos.pos].isnextdone())
      {
        if (params.dir == TPDir::LTR)
          ++travpos.pos;
        else if (params.dir == TPDir::RTL)
          --travpos.pos;
        if (travpos.pos == startpos)
        {
          travpos.pos = root->arity();
          return NULL;
        }
      }*/

    }
    else if (params.type == TPType::ORDERED)
    {
      int i;
      for (i = 0; i < constpos.childlimit(); ++i)
      {
        bool wasdone = false;
        for (;;)
        {
          if (!ro && constposchildat(i).isdone())
          {
            wasdone = true;
            // Reset our position
            travposchildat(i) = TravPos();
          }
          newexprat(i) = newtrav(rootarg(i), travposchildat(i), currdepth,
            localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);
          if (!newexprat(i) && !wasdone)
            continue;
          break;
        }
        if (wasdone)
        {
          // ro == false here
          if (!newexprat(i) || i == constpos.childlimit() - 1)
          {
            // Everything done. Return NULL.
            travpos.makenull();
            return NULL;
          }
          // Increment next position
          continue;
        }
        else
          break;
      }
      ++i;
      for (; i < constpos.childlimit(); ++i)
      {
        if (constposchildat(i).isnew())
        {
          assert(!ro);
          newtrav(rootarg(i), travposchildat(i), currdepth, localqvars,
            currnt, np(path,C,dind(i)), nextparams, mu, ro);
        }
        bool needdefer = false;
        newexprat(i) = gettrav(rootarg(i), constposchildat(i), currdepth,
          localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, false);
        /*if (needdefer)
        {
          if (constposchildat(i).isdone())
            travposchildat(i) = TravPos();
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);
        }*/
      }

      if (!ro)
      {
        bool done = true;
        for (int i = 0; i < constpos.childlimit(); ++i)
          done &= constposchildat(i).isdone();
        if (done)
          travpos.makedone();
      }
    }

    for (const auto& p : newexpr)
      if (!p)
      {
        if (!ro) travpos.makenull();
        return NULL;
      }

    ParseTree ret = ParseTree(root, std::move(newexpr), false);
    bool unused = false;
    ParseTree getret = std::move(gettrav(root, travpos, currdepth,
      localqvars, currnt, path, oldparams, unused, false));
    assert(getret == ret);
    return std::move(ret);
  }

  void fillUniqVars(const ParseTree& pt)
  {
    if (gram.isUniqueVar(pt.data()) != 0)
    {
      bool isnewvar=uniqvars[pt.data()].insert(pt.children()[0].data()).second;
      assert(isnewvar);
    }
    else
      for (const ParseTree& child : pt.children())
        fillUniqVars(child);
  }

  void handleGramMod()
  {
    assert(0 && "NewTrav doesn't support modifying Grammar mid-traversal!");
    grammodified = false;
  }

  void onGramMod(ModClass cl, ModType ty)
  {
    if (cl == ModClass::CONSTRAINT && ty == ModType::ADD)
      return;
    grammodified = true;
    lastcand = NULL;
  }
  std::shared_ptr<ModListener> mlp;

  public:

  NewTrav(Grammar &_gram, const TravParams &gp, const NTParamMap &np,
    function<bool(const Expr&, const Expr&)> sd) : gram(_gram),
    gparams(gp), ntparams(np), shoulddefer(sd), efac(gram.root->efac())
  {
    if (gparams.iterdeepen)
      currmaxdepth = 0;
    else
    {
      assert(gparams.maxrecdepth >= 0);
      currmaxdepth = gparams.maxrecdepth;
    }
    mlp.reset(new ModListener([&] (ModClass cl, ModType ty) { return onGramMod(cl, ty); }));
    bool ret = gram.addModListener(mlp);
    assert(ret);
  }

  virtual ~NewTrav()
  {
    bool ret = gram.delModListener(mlp);
    assert(ret);
  }

  virtual bool IsDone()
  {
    return IsDepthDone() && currmaxdepth == gparams.maxrecdepth;
  }

  virtual bool IsDepthDone()
  {
    if (grammodified) handleGramMod();
    return rootpos.isdone();
  }

  virtual int GetCurrDepth()
  {
    return currmaxdepth;
  }

  virtual const UniqVarMap& GetCurrUniqueVars()
  {
    return uniqvars;
  }

  virtual ParseTree GetCurrCand()
  {
    return lastcand;
  }

  virtual ParseTree Increment()
  {
    if (grammodified) handleGramMod();
    if (IsDone())
      return NULL;
    if (IsDepthDone())
    {
      rootpos = TravPos();
      gettravCache.clear();
      getfirstCache.clear();
      uniqvarnums.clear();
      lastuniqvarnum = -1;
      currmaxdepth++;
    }
    uniqvars.clear();
    lastcand = std::move(newtrav(gram.root, rootpos, 0, NULL, gram.root, rootpath, ntparams[gram.root], rootpath, false));
    lastcand.fixchildren();
    bool unused = false;
    if (lastcand)
      fillUniqVars(lastcand);
    return lastcand;
  }
};

#if DO_PATH_COLL_CHECK == 1
const Path NewTrav::rootpath = make_pair(std::hash<int>()(1), string("R"));
const Path NewTrav::nullpath = make_pair(0, string("N"));
#else
const Path NewTrav::rootpath = std::hash<int>()(1);
const Path NewTrav::nullpath = 0;
#endif

}
#endif
