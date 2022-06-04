#ifndef NEWTRAV__HPP__
#define NEWTRAV__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include "gram/TravPos.hpp"

namespace ufo
{

class NewTrav : public Traversal
{
  private:

  CFGUtils cfgutils;

  Grammar &gram;
  bool grammodified = false;
  TravParams params;
  TravPos rootpos;
  function<bool(const Expr&, const Expr&)> shoulddefer;

  ParseTree lastcand; // Not strictly necessary, but for efficiency.

  int currmaxdepth = -1;

  ParseTree gettrav(const Expr& root, const TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars,Expr currnt,bool& needdefer,bool getfirst)
  {
    CircularInt pos = travpos;
    const TravPos *nextpos = &travpos;

    if (!getfirst && travpos.isnull())
      return NULL;

    if (gram.isVar(root) || bind::isLit(root) || isOpX<FDECL>(root))
    {
      // Root is a symbolic variable
      return ParseTree(root);
    }
    else if (gram.isNt(root))
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
            return NULL;
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
          qvars, currnt, needdefer, getfirst));
        if (!getfirst) assert(ret);
        if (!ret)
        {
          if (params.order == TPOrder::FOR) ++pos;
          else if (params.order == TPOrder::REV) --pos;
          if (pos == startpos)
            return NULL;
          if (gram.isRecursive(prods[pos], root))
            newdepth = currdepth + 1;
          else
            newdepth = currdepth;
        }
      }
      assert(ret);
      needdefer= needdefer || shoulddefer(root, prods[pos]);
      return ParseTree(root, std::move(ret), true);
    }
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
      {
        // Root is a closed (quantified) variable
        return ParseTree(root);
      }
      else if (root->arity() == 1)
      {
        // Should never happen
        // There's no definition, we're expanding an empty *_VARS
        CFGUtils::noNtDefError(root, gram.root);
        return NULL;
      }
    }

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
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), *nextpos,
          currdepth, localqvars, currnt, needdefer, getfirst);
        if (!newexpr[dind(i)]) return NULL;
      }
      return ParseTree(root, std::move(newexpr), false);
    }

    if (travpos.inqueue())
    {
      assert(!getfirst);

      return gettrav(root, travpos.queueat(pos), currdepth,
        localqvars, currnt, needdefer, getfirst);
    }

    if (getfirst)
      pos = -1;

    for (int i = 0; i < root->arity(); ++i)
    {
      if (i >= travpos.min() && i != pos)
      {
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), travpos,
          currdepth, localqvars, currnt, needdefer, true);
        if (!newexpr[dind(i)]) return NULL;
      }
      else
      {
        if (!getfirst)
          nextpos = &travpos.childat(dind(i));
        newexpr[dind(i)] = gettrav(root->arg(dind(i)), *nextpos,
          currdepth, localqvars, currnt, needdefer, getfirst);
        if (!newexpr[dind(i)]) return NULL;
      }
    }

    return ParseTree(root, std::move(newexpr), false);
  }

  ParseTree newtrav(const Expr& root, TravPos& travpos,
    int currdepth, std::shared_ptr<ExprUSet> qvars, Expr currnt)
  {
    assert(("Cannot increment TravPos which is done!" && !travpos.isdone()));
    assert(("Cannot increment TravPos which is r/o!" && !travpos.readonly()));

    // Some operations should not cause copy-up; use constpos for these.
    const TravPos &constpos = travpos;

    if (gram.isVar(root) || bind::isLit(root) || isOpX<FDECL>(root))
    {
      // Root is a symbolic variable
      travpos.makedone();
      return ParseTree(root);
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

      if (params.type == TPType::STRIPED)
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

        if (gram.isRecursive(prods[travpos.pos()], root))
          newdepth = currdepth + 1;
        else
          newdepth = currdepth;

        assert(newdepth <= currmaxdepth);

        ret = ParseTree(root, std::move(newtrav(prods[travpos.pos()],
          travpos.childat(travpos.pos()), newdepth, qvars, currnt)), true);

        if (!ret.children()[0])
          // The either we picked is done at that recursive depth. Pick another.
          continue;
        break;
      }

      // Check to see if we're done.
      startpos = travpos.pos();
      CircularInt checkpos = travpos;
      while (constpos.childat(checkpos).isdone() ||
      (gram.isRecursive(prods[checkpos], root) &&
       currdepth == currmaxdepth))
      {
        if (params.order == TPOrder::FOR)
          ++checkpos;
        else if (params.order == TPOrder::REV)
          --checkpos;

        if (checkpos == startpos)
        {
          // We're done with this either; move 'pos' past end.
          travpos.makedone();
          break;
        }
      }

      assert(ret);
      bool unused = false;
      ParseTree getpt(root, std::move(gettrav(prods[constpos.pos()],
        constpos.childat(constpos.pos()), newdepth, qvars, currnt,
        unused, false)), true);
      assert(getpt == ret);
      return std::move(ret);
    }
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
      {
        // Root is a closed (quantified) variable
        travpos.makedone();
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
      travpos = TravPos(0, root->arity());

      if (params.type == TPType::STRIPED)
      {
        bool done = true;
        bool foundnull = false;
        for (int i = 0; i < travpos.childlimit(); ++i)
        {
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt);
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
      if (!travpos.inqueue())
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
      else
      {
        travpos.nextpos();
        bool done = true;
        for (int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
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
      }


      if (travpos.inqueue())
      {
        ParseTree ret(NULL);
        int startpos = travpos.pos();
        while (constpos.queueat(travpos.pos()).isdone())
        {
          travpos.queuepop();
        }

        ret = std::move(newtrav(root, travpos.queueat(travpos.pos()),
          currdepth, localqvars, currnt));
        if (!ret)
          return std::move(newtrav(root, travpos, currdepth, qvars, currnt));

        bool done = true;
        for (int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
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

        assert(ret);
        bool unused = false;
        ParseTree getpt = std::move(gettrav(root, travpos, currdepth,
          localqvars, currnt, unused, false));
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
            newexprat(i) = gettrav(rootarg(i), travpos,
              currdepth, localqvars, currnt, needdefer, true);
          }
          else
            newexprat(i) = gettrav(rootarg(i), constposchildat(i),
              currdepth, localqvars, currnt, needdefer, false);
          /*if (needdefer)
          {
            if (constposchildat(i).isdone())
              travposchildat(i) = TravPos();
            newexprat(i) = newtrav(rootarg(i), travposchildat(i),
              currdepth, localqvars, currnt);
          }*/
        }
        else
        {
          assert(!constposchildat(i).isdone());

          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt);

          if (travpos.pos() < travpos.childlimit() - 1)
          {
            TravPos *childpos = new TravPos(travpos, false);

            childpos->setmin(travpos.pos() + 1);

            if (params.prio == TPPrio::DFS)
              childpos->nextpos();

            for (int i = travpos.childmin(); i < travpos.childlimit(); ++i)
            {
              if (i == travpos.pos())
                continue;
              childpos->childat(dind(i)) = TravPos();
              newtrav(rootarg(i), childpos->childat(dind(i)),
                currdepth, localqvars, currnt);
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

      bool done = true;
      for (int i = constpos.childmin(); i < constpos.childlimit(); ++i)
        if (!constposchildat(i).isdone())
        {
          done = false;
          break;
        }
      if (done)
        for (int i = constpos.queuemin(); i < constpos.queuelimit(); ++i)
          if (!constpos.queueat(i).isdone())
          {
            done = false;
            break;
          }

      if (done)
        travpos.makedone();

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
          if (constposchildat(i).isdone())
          {
            wasdone = true;
            // Reset our position
            travposchildat(i) = TravPos();
          }
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt);
          if (!newexprat(i) && !wasdone)
            continue;
          break;
        }
        if (wasdone)
        {
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
          newtrav(rootarg(i), travposchildat(i), currdepth, localqvars,currnt);
        }
        bool needdefer = false;
        newexprat(i) = gettrav(rootarg(i), constposchildat(i),
          currdepth, localqvars, currnt, needdefer, false);
        /*if (needdefer)
        {
          if (constposchildat(i).isdone())
            travposchildat(i) = TravPos();
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt);
        }*/
      }

      bool done = true;
      for (int i = 0; i < constpos.childlimit(); ++i)
        done &= constposchildat(i).isdone();
      if (done)
        travpos.makedone();
    }

    for (const auto& p : newexpr)
      if (!p)
      {
        travpos.makenull();
        return NULL;
      }

    ParseTree ret = ParseTree(root, std::move(newexpr), false);
    bool unused = false;
    ParseTree getret = std::move(gettrav(root, travpos, currdepth,
      localqvars, currnt, unused, false));
    assert(getret == ret);
    return std::move(ret);
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

  NewTrav(Grammar &_gram, const TravParams &tp,
    function<bool(const Expr&, const Expr&)> sd) :
    gram(_gram), params(tp), shoulddefer(sd)
  {
    if (params.iterdeepen)
      currmaxdepth = 0;
    else
    {
      assert(params.maxrecdepth >= 0);
      currmaxdepth = params.maxrecdepth;
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
    return IsDepthDone() && currmaxdepth == params.maxrecdepth;
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
      currmaxdepth++;
    }
    lastcand = std::move(newtrav(gram.root, rootpos, 0, NULL, gram.root));
    return lastcand;
  }
};
}
#endif
