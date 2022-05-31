#ifndef TRAVPARAMS__HPP__
#define TRAVPARAMS__HPP__

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
  int maxrecdepth = -1;

  TravParams() {}

  TravParams(TPMethod m, TPDir d, TPOrder o, TPType t, TPPrio p, int r) :
    method(m), dir(d), order(o), type(t), prio(p), maxrecdepth(r) {}

  bool operator==(const TravParams& oth)
  {
    return method == oth.method && dir == oth.dir && order == oth.order &&
      type == oth.type && prio == oth.prio && maxrecdepth == oth.maxrecdepth;
  }
  bool operator!=(const TravParams& oth)
  {
    return method != oth.method || dir != oth.dir || order != oth.order ||
      type != oth.type || prio != oth.prio || maxrecdepth != oth.maxrecdepth;
  }

  void SetDefaults()
  {
    if (method == TPMethod::NONE) method = TPMethod::NEWTRAV;
    if (dir == TPDir::NONE)       dir = TPDir::LTR;
    if (order == TPOrder::NONE)   order = TPOrder::FOR;
    if (type == TPType::NONE)     type = TPType::STRIPED;
    if (prio == TPPrio::NONE)     prio = TPPrio::SFS;
    if (maxrecdepth < 0)          maxrecdepth = 1;
  }
};
}

#endif
