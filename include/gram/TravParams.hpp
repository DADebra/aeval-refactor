#ifndef TRAVPARAMS__HPP__
#define TRAVPARAMS__HPP__

#include <boost/logic/tribool.hpp>

namespace ufo
{
enum class TPMethod { NONE, RND, CORO, NEWTRAV };
enum class TPDir { NONE, LTR, RTL, RND };
enum class TPOrder { NONE, FOR, REV, RND };
enum class TPType { NONE, ORDERED, STRIPED };
enum class TPPrio { NONE, SFS, DFS, BFS };

struct TravParams
{
  TPMethod method = TPMethod::NONE;
  TPDir dir = TPDir::NONE;
  TPOrder order = TPOrder::NONE;
  TPType type = TPType::NONE;
  TPPrio prio = TPPrio::NONE;
  boost::tribool iterdeepen = indeterminate;
  int maxrecdepth = -2;
  boost::tribool simplify = indeterminate;
  boost::tribool propagate = indeterminate;
  boost::tribool goverride = indeterminate;

  TravParams() {}

  TravParams(TPMethod m, TPDir d, TPOrder o, TPType t, TPPrio p, tribool itd, int r, tribool s) :
    method(m), dir(d), order(o), type(t), prio(p), iterdeepen(itd), maxrecdepth(r), simplify(s) {}

  bool operator==(const TravParams& oth)
  {
    return method == oth.method && dir == oth.dir && order == oth.order &&
      type == oth.type && prio == oth.prio && bool(iterdeepen == oth.iterdeepen) &&
      maxrecdepth == oth.maxrecdepth && bool(simplify == oth.simplify) &&
      bool(propagate == oth.propagate) && bool(goverride == oth.goverride);
  }
  bool operator!=(const TravParams& oth)
  {
    return method != oth.method || dir != oth.dir || order != oth.order ||
      type != oth.type || prio != oth.prio || bool(iterdeepen != oth.iterdeepen) ||
      maxrecdepth != oth.maxrecdepth || bool(simplify != oth.simplify) ||
      bool(propagate != oth.propagate) || bool(goverride != oth.goverride);
  }

  void CopyIfUnset(const TravParams& oth)
  {
    if (method == TPMethod::NONE)   method = oth.method;
    if (dir == TPDir::NONE)         dir = oth.dir;
    if (order == TPOrder::NONE)     order = oth.order;
    if (type == TPType::NONE)       type = oth.type;
    if (prio == TPPrio::NONE)       prio = oth.prio;
    if (indeterminate(iterdeepen))  iterdeepen = oth.iterdeepen;
    if (maxrecdepth == -2)          maxrecdepth = oth.maxrecdepth;
    if (indeterminate(simplify))    simplify = oth.simplify;
    if (indeterminate(propagate))   propagate = oth.propagate;
    if (indeterminate(goverride))   goverride = oth.goverride;
  }

  void SetDefaults()
  {
    CopyIfUnset(TravParams(TPMethod::NEWTRAV, TPDir::LTR, TPOrder::FOR,
      TPType::STRIPED, TPPrio::BFS, false, 1, true));
    propagate = true;
    goverride = false;
    if (maxrecdepth == -2)
    {
      if (iterdeepen) maxrecdepth = -1;
      else maxrecdepth = 1;
    }
  }
};

typedef unordered_map<Expr,TravParams> NTParamMap;
}

#endif
