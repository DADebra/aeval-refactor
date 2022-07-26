#ifndef NEWTRAV__HPP__
#define NEWTRAV__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include "utils/TupleHash.hpp"

#include "gram/TravPos.hpp"

namespace ufo
{

class NewTrav : public Traversal
{
  private:

  CFGUtils cfgutils;
  PTSimpl ptsimpl;

  Grammar &gram;
  bool grammodified = false;
  TravParams gparams, nosimplparams;
  NTParamMap ntparams;
  TravPos rootpos;
  function<bool(const Expr&, const Expr&)> shoulddefer;

  ExprFactory& efac;

  UniqVarMap uniqvars; // Per-candidate
  unordered_map<Path, mpz_class> uniqvarnums; // Nicer unique numbers
  mpz_class lastuniqvarnum = -1;

  ParseTree lastcand; // Not strictly necessary, but for efficiency.

  int currmaxdepth = -1;

  unordered_set<Path> blacklistedPaths; // Don't go down these paths.

  // I'm not sure why, but using the Path as the key here won't work
  unordered_map<const TravPos*,ParseTree>
    gettravCache;
  unordered_map<std::tuple<Expr,int,Expr,Path,const TravParams*>,ParseTree>
    getfirstCache;

  unordered_map<const TravPos*, unordered_set<Expr>> oldCands;
  // True if all of the given NTs productions are unique
  unordered_map<std::pair<Expr,int>,tribool> _isUnique;

  inline int oldCandsSize(const TravPos* pos)
  {
    auto itr = oldCands.find(pos);
    return itr == oldCands.end() ? 0 : itr->second.size();
  }

  inline tribool& isUnique(Expr nt, int depth)
  {
    auto key = make_pair(nt, depth);
    auto itr = _isUnique.find(key);
    if (itr == _isUnique.end())
      itr = _isUnique.emplace(key, indeterminate).first;
    return itr->second;
  }

  inline void ptshoulddefer(const ParseTree& pt, bool& needdefer)
  {
    pt.foreachPt([&] (const Expr& nt, const ParseTree& expand)
    { needdefer |= shoulddefer(nt, expand.data()); });
  }

  static inline tribool isTrueFalse(Expr e)
  {
    if (isOpX<TRUE>(e))       return true;
    else if (isOpX<FALSE>(e)) return false;
    else                      return indeterminate;
  }

  ParseTree gettrav(const Expr& root, const TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars, Expr currnt, Path path, const TravParams& oldparams,
    bool& needdefer, bool getfirst, bool nocache = false)
  {
    if (blacklistedPaths.count(path) != 0)
      return NULL;

    const TravParams& params = oldparams.goverride ? oldparams :
      ntparams.count(root) != 0 ? ntparams[root] : oldparams;
    const TravParams& nextparams = oldparams.goverride ? oldparams :
      params.propagate ? params : oldparams;

    if (!getfirst && travpos.isnull())
      return NULL;

    if (gram.isVar(root) || bind::isLit(root) || gram.isConst(root) || isOpX<FDECL>(root))
      // Root is a symbolic variable
      return ParseTree(root);
    if (gram.isUniqueVar(root))
    {
      auto itr = uniqvarnums.find(path);
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

    const TravPos* key;
    std::tuple<Expr,int,Expr,size_t,const TravParams*> firstkey;
    if (!nocache)
    {
      if (!getfirst)
      {
        key = &travpos;
        auto itr = gettravCache.find(key);
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
        firstkey = std::move(make_tuple(root, currdepth, currnt, path, &oldparams));
        auto itr = getfirstCache.find(firstkey);
        if (itr != getfirstCache.end())
        {
          if (itr->second)
            ptshoulddefer(itr->second, needdefer);
          return itr->second;
        }
      }
    }

    if (getfirst)
    {
      // I'm sick of having to maintain two versions of the traversal iteration
      //   code. The rest will be pruned later.
      TravPos firstpos;
      ParseTree ret(std::move(newtrav(root, firstpos, currdepth, qvars,
        currnt, path, oldparams, path, false)));
      ptshoulddefer(ret, needdefer);
      if (!nocache) getfirstCache[firstkey] = ret;
      return std::move(ret);
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

      int newdepth;
      if (gram.isRecursive(prods[pos], root))
        newdepth = currdepth + 1;
      else
        newdepth = currdepth;

      int startpos = pos;
      ParseTree ret = NULL;
      ret = std::move(gettrav(prods[pos], travpos.childat(pos), newdepth,
        qvars, currnt, np(path,C,pos), nextparams, needdefer, getfirst, nocache));
      assert(ret);
      needdefer = needdefer || shoulddefer(root, prods[pos]);
      ret = ParseTree(root, std::move(ret), true);
      if (!nocache) gettravCache[key] = ret;
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
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), travpos.childat(dind(i)), currdepth,
          localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, getfirst, nocache);
        if (!newexpr[dind(i)])
        {
          if (!nocache) gettravCache[key] = NULL;
          return NULL;
        }
      }
    }
    else if (params.type == TPType::STRIPED)
    {
      if (travpos.inqueue())
      {
        ParseTree ret(std::move(gettrav(root, travpos.queueat(pos), currdepth,
          localqvars, currnt, np(path,Q,pos), oldparams, needdefer, getfirst, nocache)));
        if (!nocache) gettravCache[key] = ret;
        return std::move(ret);
      }

      for (int i = 0; i < root->arity(); ++i)
      {
        if (i >= travpos.min() && i != pos)
        {
          newexpr[dind(i)] = gettrav(root->arg(dind(i)), travpos.childat(dind(i)), currdepth,
            localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, true, nocache);
          if (!newexpr[dind(i)])
          {
            if (!nocache) gettravCache[key] = NULL;
            return NULL;
          }
        }
        else
        {
          newexpr[dind(i)] = gettrav(root->arg(dind(i)), travpos.childat(dind(i)), currdepth,
            localqvars, currnt, np(path,C,dind(i)), nextparams, needdefer, getfirst, nocache);
          if (!newexpr[dind(i)])
          {
            if (!nocache) gettravCache[key] = NULL;
            return NULL;
          }
        }
      }
    }

    ParseTree ret = NULL;
    if (params.simplify)
    {
      std::tie(ignore, ignore, ret) =
        std::move(ptsimpl.prunePT(root, newexpr, isTrueFalse));
    }

    if (!ret)
      ret = ParseTree(root, std::move(newexpr), false);

    if (params.simplify)
    {
      ParseTree rewriteRet = std::move(ptsimpl.rewritePT(ret, isTrueFalse));
      if (rewriteRet)
        ret = std::move(rewriteRet);
    }

    if (!nocache) gettravCache[key] = ret;
    return std::move(ret);
  }

  ParseTree newtrav(const Expr& root, TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars, Expr currnt, Path path,
    const TravParams& oldparams, Path mu, bool ro)
  {
    // mu: Only increment positions below this path
    // ro: Read-only, don't increment positions

    if (blacklistedPaths.count(path) != 0)
    {
      travpos.makenull();
      return NULL;
    }

    const TravParams& params = oldparams.goverride ? oldparams :
      ntparams.count(root) != 0 ? ntparams[root] : oldparams;
    const TravParams& nextparams = oldparams.goverride ? oldparams :
      params.propagate ? params : oldparams;

    if (path == mu)
      ro = false;

    bool alwaysro = (ro && mu == nullpath);

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
      auto itr = uniqvarnums.find(path);
      if (itr == uniqvarnums.end())
        itr = uniqvarnums.emplace(path, ++lastuniqvarnum).first;
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
        travpos.makenull();
        return NULL;
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
        oldCands.erase(&travpos); // Our address might have been used already
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
      while (true)
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
                oldCands.erase(&travpos);
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
          alwaysro ? (TravPos&)constpos.childat(travpos.pos()) :
          travpos.childat(travpos.pos()), newdepth, qvars, currnt,
          np(path,C,travpos.pos()), nextparams, mu, ro)), true);

        if (!ret.children()[0])
          // The either we picked is done at that recursive depth. Pick another.
          continue;

        bool docontinue = false;
        if (params.simplify && (prods.size() != 1 || !gram.isNt(prods[0])) &&
            !bool(isUnique(root, currdepth)))
          if (!oldCands[&travpos].insert(ret.toSortedExpr()).second)
          {
            isUnique(root, currdepth) = false;
            if (constpos.childat(travpos.pos()).isdone())
              docontinue = true; // We might be done, so check below
            else
              continue; // Definitely aren't done, can skip check below
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
          {
            oldCands.erase(&travpos);
            travpos.makedone();
            break;
          }
        }

        if (docontinue) continue;

        break;
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
    {
        if (alwaysro)
          return (TravPos&)constpos.childat(dind(i));
        else
          return travpos.childat(dind(i));
    };
    constposchildat = [&] (int i) -> const TravPos& { return constpos.childat(dind(i)); };

    bool wasnew = false;
    if (travpos.isnew())
    {
      wasnew = true;
      // First-time initialize
      assert(!ro);
      travpos = TravPos(0, root->arity());

      if (params.type == TPType::ORDERED || params.prio == TPPrio::DFS)
        travpos.nextpos();
      else if (params.type == TPType::STRIPED)
      { travpos.prevpos(); travpos.prevpos(); }
    }

    // Traversal

    ParseTree ret = NULL;
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
        ret = std::move(newtrav(root, alwaysro ?
          (TravPos&)constpos.queueat(travpos.pos()) : travpos.queueat(travpos.pos()),
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
          if (constposchildat(i).isnew())
            newexprat(i) = newtrav(rootarg(i), travposchildat(i), currdepth,
              localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);
          else
          {
            bool needdefer = false;
            if (i >= travpos.childmin())
            {
              newexprat(i) = gettrav(rootarg(i), constposchildat(i), currdepth,
                localqvars, currnt, np(path,C,dind(i)), nextparams,
                needdefer, true);
            }
            else
              newexprat(i) = gettrav(rootarg(i), constposchildat(i), currdepth,
                localqvars, currnt, np(path,C,dind(i)), nextparams,
                needdefer, false);
            /*if (needdefer)
            {
              if (constposchildat(i).isdone())
                travposchildat(i) = TravPos();
              newexprat(i) = newtrav(rootarg(i), travposchildat(i),
                currdepth, localqvars, currnt, np(path,C,dind(i)),
                nextparams, mu, ro);
            }*/
          }
        }
        else
        {
          if (!ro) assert(!constposchildat(i).isdone());

          newexprat(i) = newtrav(rootarg(i), travposchildat(i), currdepth,
            localqvars, currnt, np(path,C,dind(i)), nextparams, mu, ro);

          if (!ro && !wasnew && travpos.pos() < travpos.childlimit() - 1)
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
      for (const auto& p : newexpr)
        if (!p) { if (!ro) travpos.makenull(); return NULL; }

      if (params.simplify)
      {
        vector<int> culprits, toprune;
        std::tie(culprits, toprune, ret) =
          std::move(ptsimpl.prunePT(root, newexpr, isTrueFalse));
        if (!ro && toprune.size() != 0)
        {
          assert(toprune.size() != newexpr.size());
          assert(ret);

          bool docontinue = false;
          bool doPrune = false;
          for (const int &ci : culprits)
            if (dind(ci) < constpos.childmin())
            { doPrune = true; break; }

          if (doPrune)
          {
            // At least one of the short-circuit culprits is below
            // the min, i.e. we can't change it.
            for (const int &pi : toprune)
            {
              // This child is useless, so just set it as done so we skip
              // over it.
              if (dind(pi) >= constpos.childmin())
                travposchildat(dind(pi)).makedone();
            }
          }
          // Otherwise, no more to do, just use the new candidate
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
      for (const auto& p : newexpr)
        if (!p) { if (!ro) travpos.makenull(); return NULL; }

      if (!ro)
      {
        bool done = true;
        for (int i = 0; i < constpos.childlimit(); ++i)
          done &= constposchildat(i).isdone();
        if (done)
          travpos.makedone();
      }
    }

    if (!ret)
      ret = ParseTree(root, std::move(newexpr), false);
    if (params.simplify)
    {
      ParseTree rewriteRet = std::move(ptsimpl.rewritePT(ret, isTrueFalse));
      if (rewriteRet)
        ret = std::move(rewriteRet);
    }
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
    gparams(gp), ntparams(np), shoulddefer(sd), efac(_gram.root->efac()),
    ptsimpl(_gram.root->efac()), nosimplparams(gp)
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

    nosimplparams.simplify = false;
    nosimplparams.goverride = true;
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

  virtual ParseTree GetUnsimplifiedCand()
  {
    bool unused;
    return gettrav(gram.root, rootpos, 0, NULL, gram.root, rootpath,
      nosimplparams, unused, false, true);
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
    lastcand = std::move(newtrav(gram.root, rootpos, 0, NULL, gram.root, rootpath, gparams, rootpath, false));
    lastcand.fixchildren();
    bool unused = false;
    if (lastcand)
      fillUniqVars(lastcand);
    return lastcand;
  }

  virtual void BlacklistPath(Path p)
  { blacklistedPaths.insert(p); }

  virtual void Finish(bool success)
  {
    return;
  }
};

}
#endif
