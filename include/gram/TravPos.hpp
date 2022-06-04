#ifndef TRAVPOS__HPP__
#define TRAVPOS__HPP__

#include <vector>

namespace ufo
{
using namespace std;

struct CircularInt
{
  public:
  // min <= val < limit
  int min, val, limit;
  
  CircularInt(int _min, int _val, int _limit) :
    min(_min), val(_val), limit(_limit) {}
  CircularInt(const CircularInt& copy) :
    min(copy.min), val(copy.val), limit(copy.limit) {}

  inline operator int() const { return val; }

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
};

// A pointer which might not be owned by us
// Replacement for 'pair<bool,void*>' because that's 16 bytes (b/c alignment)
// Stems from the observation that all virtual addresses I've seen don't use the
//   top-most bit(s), so we can abuse/reuse them for other things.
uintptr_t ownedMask = (uintptr_t)1 << (8*sizeof(void*) - 1);
uintptr_t negOwnedMask = ~ownedMask;
template <typename T>
class OwnedPtr
{
  private:
  T* _ptr;

  public:

  inline bool owned() const { return (uintptr_t)_ptr & ownedMask; }

  inline void setowned(bool _owned)
  {
    if (_owned)
      _ptr = (T*)((uintptr_t)_ptr | ownedMask);
    else
      _ptr = (T*)((uintptr_t)_ptr & negOwnedMask);
  }

  inline T* ptr() const { return (T*)((uintptr_t)_ptr & negOwnedMask); }

  inline T* operator->() const { return ptr(); }

  inline T& operator*() const { return *ptr(); }

  inline operator bool() const { return bool(ptr()); }
  inline bool operator!() const { return !bool(ptr()); }

  inline bool operator==(T* oth) { return ptr() == oth; }

  inline void setptr(T* newptr)
  {
    assert(!((uintptr_t)newptr & ownedMask));
    _ptr = (T*)((uintptr_t)_ptr & ownedMask);
    _ptr = (T*)((uintptr_t)_ptr | (uintptr_t)newptr);
  }

  OwnedPtr() : _ptr(NULL) {}

  OwnedPtr(bool _owned, T* newptr)
  { setowned(_owned); setptr(newptr); }
};

class TravPos
{
  private:
  static TravPos uninitialized_pos, done_pos;

  int _min = 0, val = -2;
  uint8_t state = 0;

  // Pair is <we_own, object>; we_own is true if we can modify w/o CoW
  OwnedPtr<TravPos> *children = NULL;
  int children_size = 0;
  OwnedPtr<TravPos> *queue = NULL; // For STRIPED traversal
  int queue_size = 0, queue_cap = 0;
  std::shared_ptr<const TravPos> parent;

  void newchildren(int size)
  {
    children_size = size;
    children = (OwnedPtr<TravPos>*)malloc(sizeof(OwnedPtr<TravPos>) * size);
  }

  void newqueue(int size)
  {
    if (size == 0)
      return;
    queue_size = size;
    queue_cap = size;
    queue = (OwnedPtr<TravPos>*)malloc(sizeof(OwnedPtr<TravPos>) * size);
  }

  void copyother(const TravPos& copy, bool copyqueue)
  {
    _min = copy._min;
    val = copy.val;
    state = copy.state;
    parent = copy.parent;
    newchildren(copy.children_size);
    for (int i = 0; i < copy.children_size; ++i)
      children[i] = OwnedPtr<TravPos>(false, copy.children[i].ptr());
    if (copyqueue)
    {
      newqueue(copy.queue_size);
      for (int i = 0; i < copy.queue_size; ++i)
        queue[i] = OwnedPtr<TravPos>(false, copy.queue[i].ptr());
    }
  }

  void emptychildren()
  {
    if (!children)
      return;
    // Only deallocate any memory we own.
    for (int i = 0; i < children_size; ++i)
    {
      auto& child = children[i];
      //assert(!isdone() || !child.second || child.second->isdone());
      if (child.owned() && child)
        delete child.ptr();
    }
    delete children;
    children = nullptr;
    children_size = 0;
  }

  public:

  explicit TravPos(bool _done = false) : state(16) { if (_done) makedone(); }

  TravPos(int __min, int limit) : _min(__min)
  {
    newchildren(limit);
    for (int i = 0; i < limit; ++i)
      children[i] = OwnedPtr<TravPos>(true, nullptr);
  }

  TravPos(const TravPos& copy)
  {
    copyother(copy, true);
  }

  TravPos(TravPos& copy, bool copyqueue = true)
  {
    // If child is read-only, we can do a const-copy.
    if (copy.readonly())
    {
      copyother((const TravPos&)copy, copyqueue);
    }
    else
    {
      // Can't just set realpos to &copy; if copy changes any of its
      //   values, ours will change too (NOT what we want).
      //   Thus, we create a new (read-only) common ancestor with copy's
      //   data, and make a CoW clone of that. This necessitates changing
      //   copy, of course.

      const std::shared_ptr<const TravPos> ropos(new TravPos(std::move(copy)));
      for (int i = 0; i < ropos->children_size; ++i)
      {
        auto& child = ropos->children[i];
        if (child.owned() && child)
          child->makereadonly();
      }
      for (int i = 0; i < ropos->queue_size; ++i)
        if (ropos->queue[i].owned())
          ropos->queue[i]->makereadonly();
      copy.~TravPos();
      new (&copy) TravPos(*ropos);
      copy.parent = ropos;
      copyother(*ropos, copyqueue);
      parent = ropos;
    }
    state &= ~1;
  }

  TravPos(TravPos&& move) : _min(move._min), val(move.val), state(move.state),
    children(std::move(move.children)), queue(std::move(move.queue)),
    parent(std::move(move.parent)), children_size(move.children_size),
    queue_size(move.queue_size), queue_cap(move.queue_cap)
  {
    move.children = NULL;
    move.queue = NULL;
  }

  ~TravPos()
  { emptychildren(); emptyqueue(); }

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

  inline bool readonly() const { return state & 1; }
  inline bool isdone() const { return state & 2; }
  inline bool inqueue() const { return state & 4; }
  inline bool isnull() const { return state & 8; }
  inline bool isnew() const { return state & 16; } // Really 'uninitialized'

  inline void makereadonly() { state |= 1; }
  inline void makedone()
  {
    if (!inqueue())
      emptyqueue();
    makereadonly(); // done => readonly (we'll never increment it again)
    state |= 2;
    state &= ~16;
  }
  inline void makeinqueue() { state |= 4; val = 0; }
  inline void makenotinqueue()
  {
    state &= ~4;
    val = _min;
    emptyqueue();
  }
  inline void makenull()
  {
    state |= 8;
    makedone();
    emptychildren();
    emptyqueue();
  }

  inline int pos() const { return val; }

  inline int min() const { if (inqueue()) return 0; else return _min; }

  inline void setmin(int newmin) { _min = newmin; }

  inline int childmin() const { return _min; }
  inline int queuemin() const { return 0; }

  inline int limit() const
  { return inqueue() ? queue_size : children_size; }

  inline int childlimit() const { return children_size; }
  inline int queuelimit() const { return queue_size; }

  void nextpos()
  {
    if (val < min())
      val = min();
    else
    {
      ++val;
      if (val >= limit())
        val = min();
    }
  }

  void prevpos()
  {
    int _limit = limit();
    if (val > _limit)
      val = _limit;
    --val;
    if (val < min())
      val = _limit - 1;
  }

  operator CircularInt() const
  { return CircularInt(min(), pos(), limit()); }

  inline const TravPos& childat(int pos) const
  {
    if (isdone() && pos >= children_size)
      pos = 0;
    auto& child = children[pos];
    if (!child)
    {
      return uninitialized_pos;
    }
    return *child;
  }

  inline TravPos& childat(int pos)
  {
    if (isdone() && pos >= children_size)
      pos = 0;
    auto& child = children[pos];
    if (!child)
      child.setptr(new TravPos());
    else if (!child.owned())
      child.setptr(new TravPos(*child));
    child.setowned(true);
    child->state &= ~1;
    return *child;
  }

  // For NTs
  inline void childpop()
  {
    auto& child = children[val];
    if (child == &done_pos)
      return;
    if (child.owned())
      delete child.ptr();
    child.setowned(false);
    child.setptr(&done_pos);
  }

  inline const TravPos& queueat(int pos) const
  {
    return *queue[pos];
  }

  inline TravPos& queueat(int pos)
  {
    assert(queue[pos]);
    if (!queue[pos].owned())
      queue[pos] = OwnedPtr<TravPos>(true, new TravPos(*queue[pos]));
    return *queue[pos];
  }

  inline void queuepush_back(TravPos* newpos)
  {
    // Takes ownership of newpos
    ++queue_size;
    if (queue_size > queue_cap)
    {
      if (queue_cap == 0)
        queue_cap = children_size;
      else
        queue_cap *= 2;
      queue = (OwnedPtr<TravPos>*)realloc(queue, sizeof(OwnedPtr<TravPos>) * queue_cap);
    }
    queue[queue_size - 1] = OwnedPtr<TravPos>(true, newpos);
  }

  inline void emptyqueue()
  {
    if (!queue)
      return;
    for (int i = 0; i < queue_size; ++i)
    {
      //assert(!isdone() || !que.second || que.second->isdone());
      if (queue[i].owned())
        delete queue[i].ptr();
    }
    delete queue;
    queue = nullptr;
    queue_size = 0;
    queue_cap = 0;
  }

  inline void queuepop()
  {
    auto& que = queue[val];
    if (que.owned())
      delete que.ptr();
    if (val == queue_size - 1)
    {
      --queue_size;
      val = 0;
    }
    else
    {
      que.setowned(false);
      que.setptr(&done_pos);
      nextpos();
    }
    if (queue_size == 0)
      emptyqueue();
  }
};

TravPos TravPos::uninitialized_pos;
TravPos TravPos::done_pos(true);

}
#endif
