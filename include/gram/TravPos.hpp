#ifndef TRAVPOS__HPP__
#define TRAVPOS__HPP__

#include <vector>
#include <deque>

namespace ufo
{
using namespace std;
struct TravPos;

struct CircularInt
{
  public:
  // min <= val < limit
  int min, val, limit;
  
  CircularInt() : min(0), val(-2), limit(0) {}
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
  static TravPos uninitialized_pos, done_pos;

  // Pair is <we_own, object>; we_own is true if we can modify w/o CoW
  vector<pair<bool,TravPos*>> children;
  deque<pair<bool,TravPos*>> queue; // For STRIPED traversal
  bool readonly = false;
  std::shared_ptr<const TravPos> parent;

  void copyother(const TravPos& copy, bool copyqueue)
  {
    pos = copy.pos;
    children.reserve(copy.children.size());
    for (auto &child : copy.children)
      children.emplace_back(false, child.second);
    if (copyqueue)
    {
      oldmin = copy.oldmin;
      for (auto &que : copy.queue)
        queue.emplace_back(false, que.second);
    }
  }

  void clearchildren()
  {
    // Only deallocate any memory we own.
    for (auto &child : children)
    {
      //assert(!isdone() || !child.second || child.second->isdone());
      if (child.first && child.second)
      {
        delete child.second;
        child.second = NULL;
      }
    }
    children.clear();
    children.shrink_to_fit();
  }

  public:
  CircularInt pos;
  int oldmin = -1;

  TravPos() {}

  TravPos(int min, int limit) : pos(min, -1, limit)
  {
    if (limit > 0)
    {
      children.reserve(limit);
      for (int i = 0; i < limit; ++i)
        children.emplace_back(true, nullptr);
    }
  }

  TravPos(const TravPos& copy) : parent(copy.parent)
  {
    copyother(copy, true);
  }

  TravPos(TravPos& copy, bool copyqueue = true)
  {
    // If child is read-only, we can do a const-copy.
    if (copy.readonly)
    {
      copyother((const TravPos&)copy, copyqueue);
      parent = copy.parent;
    }
    else
    {
      // Can't just set realpos to &copy; if copy changes any of its
      //   values, ours will change too (NOT what we want).
      //   Thus, we create a new (read-only) common ancestor with copy's
      //   data, and make a CoW clone of that. This necessitates changing
      //   copy, of course.

      const std::shared_ptr<const TravPos> ropos(new TravPos(std::move(copy)));
      for (auto &child : ropos->children)
        if (child.first && child.second)
          child.second->readonly = true;
      for (auto &que : ropos->queue)
        if (que.first)
          que.second->readonly = true;
      copy.~TravPos();
      new (&copy) TravPos(*ropos);
      copy.parent = ropos;
      copyother(*ropos, copyqueue);
      parent = ropos;
    }
  }

  TravPos(TravPos&& move) : pos(move.pos),
    children(std::move(move.children)), queue(std::move(move.queue)),
    oldmin(move.oldmin), parent(std::move(move.parent)) {}

  ~TravPos()
  { clearchildren(); emptyqueue(); }

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
    if (isdone() && pos >= children.size())
      pos = 0;
    auto& child = children[pos];
    if (!child.second)
    {
      return uninitialized_pos;
    }
    return *child.second;
  }

  inline TravPos& childat(int pos)
  {
    if (isdone() && pos >= children.size())
      pos = 0;
    auto& child = children[pos];
    if (!child.second)
      child.second = new TravPos();
    else if (!child.first)
      child.second = new TravPos(*child.second);
    child.first = true;
    return *child.second;
  }

  inline int childrensize() const
  {
    return children.size();
  }

  // For NTs
  inline void childpop()
  {
    auto& child = children[pos];
    if (child.first)
      delete child.second;
    child.first = false;
    child.second = &done_pos;
  }

  inline const TravPos& queueat(int pos) const
  {
    if (!queue[pos].second)
      return done_pos;
    return *queue[pos].second;
  }

  inline TravPos& queueat(int pos)
  {
    assert(queue[pos].second);
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
    return queue.emplace_back(true, newpos);
  }

  inline void emptyqueue()
  {
    for (auto &que : queue)
    {
      //assert(!isdone() || !que.second || que.second->isdone());
      if (que.first)
      {
        delete que.second;
        que.second = NULL;
      }
    }
    queue.clear();
    queue.shrink_to_fit();
  }

  inline void queuepop()
  {
    if (queue[pos].first)
      delete queue[pos].second;
    if (pos == 0)
    {
      queue.pop_front();
      --pos.limit;
    }
    else if (pos == queue.size() - 1)
    {
      queue.pop_back();
      --pos.limit;
      pos = 0;
    }
    else
    {
      queue[pos].second = NULL;
      ++pos;
    }
    if (queue.size() == 0)
      queue.shrink_to_fit();
  }

  inline bool isdone() const
  {
    return pos.limit == -2;
  }

  inline void makedone()
  {
    if (!inqueue())
      emptyqueue();
    pos.limit = -2;
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
  friend class NewTrav;
};

TravPos TravPos::uninitialized_pos;
TravPos TravPos::done_pos(0, -2);

}
#endif
