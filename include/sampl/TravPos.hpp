#ifndef TRAVPOS__HPP__
#define TRAVPOS__HPP__
namespace ufo
{
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
}
#endif
