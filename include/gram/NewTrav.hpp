#ifndef NEWTRAV__HPP__
#define NEWTRAV__HPP__

#include "gram/ParseTree.hpp"
#include "gram/TravPos.hpp"
#include "gram/TravParams.hpp"
#include "gram/Grammar.hpp"

namespace ufo
{

class NewTrav : public Traversal
{
  private:

  Grammar &gram;
  TravParams params;
  TravPos rootpos;
  function<bool(const Expr&, const Expr&)> shoulddefer;

  ParseTree gettrav(const Expr& root, const TravPos& travpos, int currdepth,
    std::shared_ptr<ExprUSet> qvars,Expr currnt,bool& needdefer,bool getfirst)
  {
    CircularInt pos(travpos.pos);
    pos.min = 0;
    const TravPos *nextpos = &travpos;

    if (!getfirst && travpos.pos == -3)
      return NULL;

    if (gram.isVar(root) || bind::isLit(root) || gram.isConst(root))
    {
      // Root is a symbolic variable
      return ParseTree(root);
    }
    else if (gram.isNt(root))
    {
      if (root != currnt)
        currdepth = 0;
      currnt = root;
      const auto& prods = gram.prods.at(root);
      pos.limit = prods.size();
      if (getfirst)
      {
        if (params.order == TPOrder::FOR)
          pos = 0;
        else if (params.order == TPOrder::REV)
          pos = prods.size() - 1;
        int startpos = pos;
        while (CFGUtils::isRecursive(prods[pos], root) &&
          currdepth == params.maxrecdepth)
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
      if (CFGUtils::isRecursive(prods[pos], root))
        newdepth = currdepth + 1;
      else
        newdepth = currdepth;

      int startpos = pos;
      ParseTree ret = NULL;
      while (!ret)
      {
        ret = gettrav(prods[pos], *nextpos, newdepth,
          qvars, currnt, needdefer, getfirst);
        if (!getfirst) assert(ret);
        if (!ret)
        {
          if (params.order == TPOrder::FOR) ++pos;
          else if (params.order == TPOrder::REV) --pos;
          if (pos == startpos)
            return NULL;
          if (CFGUtils::isRecursive(prods[pos], root))
            newdepth = currdepth + 1;
          else
            newdepth = currdepth;
        }
      }
      assert(ret);
      needdefer= needdefer || shoulddefer(root, prods[pos]);
      return ParseTree(root, vector<ParseTree>{ret}, true);
    }
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
      {
        // Root is a closed (quantified) variable
        return ParseTree(root);
      }
      else
      {
        // Should never happen
        // There's no definition, we're expanding an empty *_VARS
        CFGUtils::noNtDefError(root, gram.root);
        return NULL;
      }
    }

    // Root is a Z3 function (e.g. (and ...))
    pos.limit = root->arity();
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

    if (!getfirst)
      assert(travpos.childrensize() == root->arity());
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

    if (travpos.inqueue() && travpos.pos.limit != -1)
    {
      assert(!getfirst);

      return gettrav(root, travpos.queueat(pos), currdepth,
        localqvars, currnt, needdefer, getfirst);
    }

    if (getfirst)
      pos = -1;

    for (int i = 0; i < root->arity(); ++i)
    {
      if (i >= travpos.pos.min && i != pos)
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

    // Some operations should not cause copy-up; use constpos for these.
    const TravPos &constpos = travpos;

    if (gram.isVar(root) || bind::isLit(root))
    {
      // Root is a symbolic variable
      travpos = TravPos(0, 1);
      ++travpos.pos;
      travpos.makedone();
      return ParseTree(root);
    }
    else if (gram.isNt(root))
    {
      if (root != currnt)
        currdepth = 0;
      currnt = root;
      const auto &prods = gram.prods.at(root);
      if (prods.size() == 0)
      {
        CFGUtils::noNtDefError(root, gram.root);
        return NULL; // Unreachable
      }

      if (travpos.pos < 0)
      {
        // First-time initialize
        travpos = TravPos(0, prods.size());
        if (params.type != TPType::STRIPED)
        {
          if (params.order == TPOrder::FOR)
            ++travpos.pos;
          else if (params.order == TPOrder::REV)
            --travpos.pos;
        }
      }

      if (params.type == TPType::STRIPED)
      {
        if (params.order == TPOrder::FOR)
          ++travpos.pos;
        else if (params.order == TPOrder::REV)
          --travpos.pos;
      }

      // We're just checking, use const version of queueat()
      CircularInt checkpos = constpos.pos;

      int startpos = checkpos;
      /*while (constpos.childat(checkpos).isdone() ||
      (CFGUtils::isRecursive(prods[checkpos], root) &&
       currdepth == params.maxrecdepth))
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
      for (;;)
      {
        while (constpos.childat(checkpos).isdone() ||
         (checkprio && shoulddefer(root, prods[checkpos])) ||
         (CFGUtils::isRecursive(prods[checkpos], root) &&
         currdepth == params.maxrecdepth))
        {
          if (params.order == TPOrder::FOR)
            ++checkpos;
          else if (params.order == TPOrder::REV)
            --checkpos;

          if (checkpos == startpos)
          {
            if (checkprio)
              // All productions must be deferred; pick first one
              checkprio = false;
            else
            {
              travpos.pos = -3;
              travpos.makedone();
              return NULL;
            }
          }
        }

        travpos.pos = checkpos;

        if (CFGUtils::isRecursive(prods[travpos.pos], root))
          newdepth = currdepth + 1;
        else
          newdepth = currdepth;

        assert(newdepth <= params.maxrecdepth);

        ret = ParseTree(root, vector<ParseTree>{newtrav(prods[travpos.pos],
          travpos.childat(travpos.pos), newdepth, qvars, currnt)}, true);

        if (!ret.children()[0])
          // The either we picked is done at that recursive depth. Pick another.
          continue;
        break;
      }

      // Check to see if we're done.
      checkpos = travpos.pos;
      while (constpos.childat(checkpos).isdone() ||
      (CFGUtils::isRecursive(prods[checkpos], root) &&
       currdepth == params.maxrecdepth))
      {
        if (params.order == TPOrder::FOR)
          ++checkpos;
        else if (params.order == TPOrder::REV)
          --checkpos;

        if (checkpos == travpos.pos)
        {
          // We're done with this either; move 'pos' past end.
          travpos.makedone();
          break;
        }
      }

      assert(ret);
      bool unused = false;
      ParseTree getpt = ParseTree(root,
        vector<ParseTree>{gettrav(prods[constpos.pos],
        constpos.childat(constpos.pos), newdepth, qvars, currnt,
        unused, false)}, true);
      assert(getpt == ret);
      return ret;
    }
    else if (isOpX<FAPP>(root))
    {
      if (qvars != NULL && qvars->find(root->left()) != qvars->end())
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

    if (travpos.pos == -2 && !travpos.inqueue())
    {
      // First-time initialize
      travpos = TravPos(0, root->arity());

      if (params.type == TPType::STRIPED)
      {
        bool done = true;
        bool foundnull = false;
        for (int i = 0; i < travpos.childrensize(); ++i)
        {
          newexprat(i) = newtrav(rootarg(i), travposchildat(i),
            currdepth, localqvars, currnt);
          if (!newexprat(i))
            foundnull = true;
          bool idone = constposchildat(i).isdone();
          if (idone && i == travpos.pos)
            ++travpos.pos;
          done &= idone;
        }
        if (done)
          travpos.makedone();
        else if (params.prio == TPPrio::DFS)
          ++travpos.pos;

        if (foundnull)
        {
          travpos.pos = -3;
          travpos.makedone();
          return NULL;
        }

        return ParseTree(root, std::move(newexpr), false);
      }
      else
        ++travpos.pos;
    }

    // Traversal

    if (params.type == TPType::STRIPED)
    {
      if (!travpos.inqueue())
      {
        if (params.prio != TPPrio::DFS)
        {
          ++travpos.pos;
          if (travpos.pos == travpos.pos.min &&
          params.prio == TPPrio::BFS &&
          constpos.queuesize() != 0)
            travpos.makeinqueue();
          else
          {
            int startpos = travpos.pos;
            while (constposchildat(travpos.pos).isdone())
            {
              ++travpos.pos;
              if (travpos.pos == startpos ||
              (params.prio == TPPrio::BFS &&
              travpos.pos == travpos.pos.min))
              {
                if (constpos.queuesize() != 0)
                  travpos.makeinqueue();
                break;
              }
            }
          }
        }
        else if (constposchildat(travpos.pos).isdone())
        {
          ++travpos.pos;
          if (travpos.pos == travpos.pos.min)
          {
            assert(constpos.queuesize() != 0);
            travpos.makeinqueue();
          }
        }
      }
      else
      {
        bool done = true;
        for (int i = 0; i < constpos.queuesize(); ++i)
          done &= constpos.queueat(i).isdone();
        if (done)
        {
          for (int i = travpos.oldmin; i < travpos.childrensize(); ++i)
            done &= constposchildat(i).isdone();
          if (done)
          {
            travpos.pos = -3;
            travpos.makedone();
            return NULL;
          }
          travpos.makenotinqueue();
        }
      }


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
          currdepth, localqvars, currnt);
        if (!ret)
          return newtrav(root, travpos, currdepth, qvars, currnt);

        bool done = true;
        checkpos = travpos.pos;
        for (int i = 0; i < constpos.queuesize(); ++i)
          done &= constpos.queueat(i).isdone();
        if (done)
        {
          if (params.prio != TPPrio::BFS)
            travpos.makedone();
          else
          {
            for (int i = travpos.oldmin; i < travpos.childrensize(); ++i)
              done &= constposchildat(i).isdone();
            if (done)
              travpos.makedone();
          }
        }

        assert(ret);
        bool unused = false;
        ParseTree getpt= gettrav(root, travpos, currdepth, localqvars, currnt,
          unused, false);
        assert(getpt == ret);
        return ret;
      }
      else if (travpos.pos.limit == -1)
      {
        travpos.pos = travpos.pos.min;
        travpos.pos.limit = root->arity();
        while (constposchildat(travpos.pos).isdone())
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
          assert(constposchildat(i).pos != -2);
          bool needdefer = false;
          if (i >= travpos.pos.min || constposchildat(i).pos == -2)
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

          if (travpos.pos < root->arity() - 1)
          {
            TravPos *childpos = new TravPos(travpos, false);

            childpos->pos = CircularInt(travpos.pos + 1,
                travpos.pos, root->arity());

            if (params.prio == TPPrio::DFS)
              ++childpos->pos;

            for (int i = travpos.pos.min; i < travpos.pos.limit; ++i)
            {
              if (i == travpos.pos)
                continue;
              childpos->childat(dind(i)) = TravPos();
              newtrav(rootarg(i), childpos->childat(dind(i)),
                currdepth, localqvars, currnt);
            }

            bool done = true;
            const TravPos *constchild = (const TravPos*)childpos;
            for (int i= childpos->pos.min; i < childpos->pos.limit; ++i)
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
      for (int i = constpos.pos.min; i < constpos.childrensize(); ++i)
        if (!constposchildat(i).isdone())
        {
          done = false;
          break;
        }
      if (done)
        for (int i = 0; i < constpos.queuesize(); ++i)
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
      for (i = 0; i < root->arity(); ++i)
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
          if (!newexprat(i) || i == root->arity() - 1)
          {
            // Everything done. Return NULL.
            travpos.pos = -3;
            travpos.makedone();
            return NULL;
          }
          // Increment next position
          continue;
        }
        else
          break;
      }
      ++i;
      for (; i < root->arity(); ++i)
      {
        if (constposchildat(i).pos == -2)
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
      for (int i = 0; i < root->arity(); ++i)
        done &= constposchildat(i).isdone();
      if (done)
        travpos.makedone();
    }

    for (const auto& p : newexpr)
      if (!p)
      {
        travpos.pos = -3;
        travpos.makedone();
        return NULL;
      }

    ParseTree ret = ParseTree(root, newexpr, false);
    bool unused = false;
    ParseTree getret = gettrav(root, travpos, currdepth,
      localqvars, currnt, unused, false);
    assert(getret == ret);
    return std::move(ret);
  }

  void onGramMod(ModClass cl, ModType ty)
  {
    if (cl != ModClass::CONSTRAINT)
      assert(0 && "NewTrav doesn't support modifying Grammar mid-traversal!");
  }
  ModListener ml; std::shared_ptr<ModListener> mlp;

  public:

  NewTrav(Grammar &_gram, const TravParams &tp,
    function<bool(const Expr&, const Expr&)> sd) :
    gram(_gram), params(tp), shoulddefer(sd)
  {
    ml = [&] (ModClass cl, ModType ty) { return onGramMod(cl, ty); };
    bool ret = gram.addModListener(mlp);
    assert(ret);
  }

  ~NewTrav()
  {
    bool ret = gram.delModListener(mlp);
    assert(ret);
  }

  virtual bool IsDone() { return rootpos.isdone(); }

  virtual ParseTree GetCurrCand()
  {
    bool needdefer = false;
    ParseTree ret = gettrav(gram.root,rootpos,0,NULL,gram.root,needdefer,false);
    ret.fixchildren();
    return ret;
  }

  virtual ParseTree Increment()
  {
    if (IsDone())
      return NULL;
    ParseTree ret = newtrav(gram.root, rootpos, 0, NULL, gram.root);
    ret.fixchildren();
    return std::move(ret);
  }
};
}
#endif
