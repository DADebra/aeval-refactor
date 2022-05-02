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
  TPMethod method;
  TPDir dir;
  TPOrder order;
  TPType type;
  TPPrio prio;
  int maxrecdepth;
};
}

#endif
