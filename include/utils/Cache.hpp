#ifndef __CACHE__HPP__
#define __CACHE__HPP__

#include <unordered_map>
#include <set>
#include <deque>
#include <vector>
#include <tuple>
#include <type_traits>

struct CacheNoUpdate
{
  template <typename T, typename U>
  void operator()(const T& t, U& u) const { return; }
};

struct CacheNoCompare
{
  template <typename T, typename U>
  bool operator()(const T& lt, const U& lu, const T& rt, const U& ru) const
  { return false; }
};

class CacheNoCompType {} __cachenocomptype;

// A limited-size cache, which will prune the 'least' element on overflow.
// Maps `K` to `V`, storing `CompType` (if not CacheNoCompType) along with
//   each `V`.
// Use a capacity of `-1` for unlimited size (though this is less efficient
//   than a standard unordered_map/unordered_set and probably pointless).
// Calls `void Update(const V&, CompType&)` on each read
//   (if not CacheNoUpdate).
// Uses `bool Compare(const V& lv, const CompType& lc, const V& rv,
//   const CompType& rc)` to determine which element is 'least'.
//   If CacheNoCompare, this element is that which was inserted first.
// If `K` is void, then the class acts like a set.
// `CompType` must be default constructable (and is on insertion).
// If `CompType` is given, iterators point towards an internal class `ValuePair`
//   which has fields `val` (for V) and `extra` (for CompType) and is
//   implicitly convertible to V (though an explicit cast might be necessary).
// See comments on functions for complexity: in general, this container is
//   optimized for access speed and insertion.
template <typename K, typename V, typename CompType,
         typename Update, typename Compare>
class Cache
{
  public:
  typedef Cache<K,V,CompType,Update,Compare> this_type;
  struct ValuePair
  {
    V val;
    CompType extra;

    ValuePair() : val(), extra() {}
    explicit ValuePair(V&& _val) : val(std::move(_val)), extra() {}
    explicit ValuePair(const V& _val) : val(_val), extra() {}
    ValuePair(ValuePair&& oth) :
      val(std::move(oth.val)), extra(std::move(oth.extra)) {}
    ValuePair(const ValuePair& oth) :
      val(oth.val), extra(oth.extra) {}

    // For external users
    operator V&() { return val; }
    V&& moveval() { return std::move(val); }
    operator const V&() const { return val; }

    bool operator==(const ValuePair& oth) const
    { return oth.val == val; }
    bool operator!=(const ValuePair& oth) const
    { return ! (*this == oth); }
  };

  typedef typename std::conditional< std::is_same<K, void>::value,
    V,
    K>::type key_type;

  typedef typename std::conditional< std::is_same<CompType, CacheNoCompType>::value,
    V,
    ValuePair>::type mapped_type;
  
  private:
  struct ValuePairHash
  {
    size_t operator()(const ValuePair& vp) const { return std::hash<V>()(vp.val); }
  };

  static const V& val(const V& v) { return v; }
  static const V& val(const ValuePair& v) { return v.val; }
  static V& val(V& v) { return v; }
  static V& val(ValuePair& v) { return v.val; }

  static const CompType& extra(const V& v) { return __cachenocomptype; }
  static CompType& extra(const ValuePair& v) { return (CompType&)v.extra; }

  private:
  typedef typename std::conditional< std::is_same<K, void>::value,
    V,
    std::pair<const key_type, V>>::type insert_type;

  typedef typename std::conditional< std::is_same<K, void>::value,
    typename std::conditional< std::is_same<CompType, CacheNoCompType>::value,
      const V&,
      ValuePair>::type,
    const key_type&>::type real_key_type;

  typedef typename std::conditional< std::is_same<K, void>::value,
    typename std::conditional< std::is_same<CompType, CacheNoCompType>::value,
      std::hash<V>,
      ValuePairHash>::type,
    std::hash<key_type>>::type hash_type;

  typedef typename std::conditional< std::is_same<K, void>::value,
    std::unordered_set<mapped_type, hash_type>,
    std::unordered_map<key_type, mapped_type, hash_type>>::type Container;

  public:
  typedef typename Container::value_type value_type;

  private:
  static const real_key_type& getkey(const typename std::unordered_set<mapped_type, hash_type>::value_type& s)
  { return s; }
  static const real_key_type& getkey(const typename std::unordered_map<key_type, mapped_type, hash_type>::value_type& s)
  { return s.first; }
  static const mapped_type& getmapped(const typename std::unordered_set<mapped_type, hash_type>::value_type& s)
  { return s; }
  static const mapped_type& getmapped(const typename std::unordered_map<key_type, mapped_type, hash_type>::value_type& s)
  { return s.second; }

  static const mapped_type& deref(const typename std::unordered_set<mapped_type, hash_type>::iterator& s)
  { return *s; }
  static mapped_type& deref(typename std::unordered_set<mapped_type, hash_type>::iterator& s)
  { return (mapped_type&)*s; }
  static const mapped_type& deref(const typename std::unordered_map<key_type, mapped_type, hash_type>::iterator& s)
  { return s->second; }
  static mapped_type& deref(typename std::unordered_map<key_type, mapped_type, hash_type>::iterator& s)
  { return (mapped_type&)s->second; }

  struct OrderCompare
  {
    Compare compare;
    bool operator()(const value_type* l, const value_type* r) const
    { const mapped_type &lm = this_type::getmapped(*l),
                        &rm = this_type::getmapped(*r);
      return compare(this_type::val(lm), this_type::extra(lm),
        this_type::val(rm), this_type::extra(rm)); }
  };

  typedef typename std::conditional<
    std::is_same<CompType, CacheNoCompType>::value,
    typename std::conditional< std::is_same<Compare, CacheNoCompare>::value,
      std::deque<const value_type*>,
      std::multiset<const value_type*,OrderCompare>>::type,
    std::multiset<const value_type*,OrderCompare> >::type OrderContainer;

  typedef typename OrderContainer::iterator orditerator;

  std::pair<orditerator,bool> ordadd(const std::deque<const value_type*>& con, const value_type* val)
  { order.push_back(val); return make_pair(--order.end(), true); }
  std::pair<orditerator,bool> ordadd(const std::multiset<const value_type*,OrderCompare>& con, const value_type* val)
  { return make_pair(order.insert(val), true); }
  orditerator ordfind(const std::deque<const value_type*>& con, const value_type* val)
  { orditerator ret;
    for (ret = order.begin(); *ret != val && ret != order.end(); ++ret);
    return ret; }
  orditerator ordfind(const std::multiset<const value_type*,OrderCompare>& con, const value_type* val)
  { return order.find(val); }
  size_t orderase(const std::deque<const value_type*>& con, const value_type* val)
  {
    orditerator itr = ordfind(con, val);
    if (itr == order.end()) return 0;
    order.erase(itr);
    return 1;
  }
  size_t orderase(const std::multiset<const value_type*,OrderCompare>& con, const value_type* val)
  { return order.erase(val); }

  public:
  class iterator
  {
    orditerator real_itr;

    public:
    iterator() : real_itr() {}
    iterator(const orditerator& itr) : real_itr(itr) {}
    iterator(orditerator&& itr) : real_itr(std::move(itr)) {}
    iterator(const iterator& oth) : real_itr(oth.real_itr) {}
    iterator(iterator&& oth) : real_itr(std::move(oth.real_itr)) {}

    const value_type& operator*() const { return **real_itr; }
    const value_type* operator->() const { return &**real_itr; }

    bool operator==(const iterator& oth) const
    { return real_itr == oth.real_itr; }
    bool operator!=(const iterator& oth) const { return !(*this == oth); }

    // Prefix
    iterator& operator++() { ++real_itr; return *this; }
    iterator& operator--() { --real_itr; return *this; }

    // Postfix
    iterator& operator++(int) { iterator copy(*this); ++real_itr; return copy; }
    iterator& operator--(int) { iterator copy(*this); --real_itr; return copy; }

    friend Cache;
  };
  typedef const iterator const_iterator;
  iterator begin() { return iterator(order.begin()); }
  iterator end() { return iterator(order.end()); }
  const iterator begin() const { return iterator(order.begin()); }
  const iterator end() const { return iterator(order.end()); }
  const iterator cbegin() { return iterator(order.begin()); }
  const iterator cend() { return iterator(order.end()); }

  private:
  Container cache;
  OrderContainer order;
  size_t _capacity;
  Update update;

  template <typename T>
  void ordupdate(const T& con, const CacheNoUpdate& upd,
    typename Container::iterator& itr) {}

  void ordupdate(const std::multiset<const value_type*,OrderCompare>& con,
    const Update& upd, typename Container::iterator& itr)
  {
    mapped_type &vm = deref(itr);
    // Re-insert so it has the right position
    auto itrrange = order.equal_range(&*itr);
    for (auto orditr = itrrange.first; orditr != itrrange.second; ++orditr)
      if (**orditr == *itr)
      {
        order.erase(orditr);
        update(val(vm), extra(vm));
        order.insert(&*itr);
        return;
      }
    assert(0); // Should never happen
  }

  std::pair<iterator,bool> vinsert(value_type&& v)
  {
    auto cacheret = cache.insert(std::move(v));
    mapped_type& ref = deref(cacheret.first);
    if (!cacheret.second)
    {
      ordupdate(order, update, cacheret.first);
      return make_pair(order.end(), false);
    }
    update(val(ref), extra(ref)); // Not yet inserted to order, so safe

    if (_capacity > 0 && cache.size() >= _capacity)
      pop();

    auto ret = ordadd(order, &*cacheret.first);
    assert(ret.second);
    assert(cache.size() == order.size());
    return std::move(ret);
  }

  public:
  Cache(size_t __capacity) : _capacity(__capacity) {}

  // O(1) if no compare and no update, O(log n) otherwise
  template<typename T>
  std::pair<iterator,bool> insert(T&& v)
  {
    return vinsert(std::move(value_type(std::forward<T>(v))));
  }

  // O(1) if no compare and no update, O(log n) otherwise
  template <typename... Args>
  std::pair<iterator,bool> emplace(Args&&... args)
  {
    return vinsert(std::move(value_type(args...)));
  }

  // O(1)
  value_type pop()
  {
    auto cachetop = cache.find(getkey(**order.begin()));
    assert(cachetop != cache.end());
    value_type ret(std::move(*cachetop));
    // Will result in a second call to V's dtor
    cache.erase(cachetop);
    order.erase(order.begin());
    return std::move(ret);
  }

  // O(1): The 'least' element
  const value_type& top() const
  { return **order.begin(); }

  // O(1): The 'greatest' element
  const value_type& bottom() const
  { return **(--order.end()); }

  bool empty() const { return cache.empty(); }

  // O(1) if no update, O(log n) otherwise
  mapped_type& operator[](const key_type& key)
  {
    static_assert(!std::is_same<K, void>::value,
      "operator[] cannot be used with sets");
    auto itr = cache.find((real_key_type)key);
    if (itr == cache.end())
      return (mapped_type&)*emplace((real_key_type)key, V()).first;
    else
      ordupdate(order, update, itr);
    return deref(itr);
  }

  // O(1) if no update, O(log n) otherwise
  mapped_type& at(const key_type& key)
  {
    static_assert(!std::is_same<K, void>::value,
      "at() cannot be used with sets");
    auto itr = cache.find((real_key_type)key);
    if (itr == cache.end())
      throw std::out_of_range("Cache::at()");
    update(val(deref(itr)), extra(deref(itr)));
    return deref(itr);
  }

  // O(1)
  const mapped_type& at(const key_type& key) const
  {
    static_assert(!std::is_same<K, void>::value,
      "at() cannot be used with sets");
    return cache.at((real_key_type)key);
  }

  // O(1)
  size_t count(const key_type& key) const
  { return cache.count((real_key_type)key); }

  // O(n) if no comptype and no update/compare, O(log n) otherwise
  iterator find(const key_type& key)
  {
    auto cacheitr = cache.find((real_key_type)key);
    if (cacheitr == cache.end())
      return order.end();
    auto orditr = ordfind(order, &*cacheitr);
    assert(orditr != order.end());
    return std::move(orditr);
  }

  // O(1)
  iterator erase(const_iterator pos)
  {
    iterator ret = order.erase(pos.real_itr);
    cache.erase(getkey(*pos));
    return std::move(ret);
  }

  // O(n) if no comptype and no update/compare, O(log n) otherwise
  size_t erase(const key_type& key)
  {
    auto cacheitr = cache.find((real_key_type)key);
    if (cacheitr == cache.end())
      return 0;
    size_t oret = orderase(order, &*cacheitr);
    assert(oret == 1);
    cache.erase(cacheitr);
    return 1;
  }

  // O(n)
  void resize(size_t newsize)
  {
    if (newsize < 0 || newsize > cache.size())
      return;
    while (cache.size() > newsize)
      pop();
  }

  // O(n)
  void set_capacity(size_t newcap)
  {
    _capacity = newcap;
    if (_capacity >= 0)
      resize(_capacity);
  }

  size_t capacity() const { return _capacity; }

  size_t size() const { return cache.size(); }
  size_t max_size() const { return _capacity; }

  // Probably O(n)
  void clear()
  {
    cache.clear();
    order.clear();
  }
};

// A 'Least-Recently-Created' cache which pops elements which were added first.
template <typename K, typename V>
using LRCCache = Cache<K,V,CacheNoCompType,CacheNoUpdate,CacheNoCompare>;
template <typename V>
using LRCSet = Cache<void,V,CacheNoCompType,CacheNoUpdate,CacheNoCompare>;

struct RUUpdate
{
  int RUTime = 0; // No reason to use system time
  template <typename V>
  void operator()(const V& val, int &time) { time = ++RUTime; }
};

struct FUUpdate
{
  template <typename V>
  void operator()(const V& val, int &usecount) const { ++usecount; }
};

template <typename V, typename CompType>
struct CompLess
{
  bool operator()(const V& lv, const CompType& lc,
    const V& rv, const CompType& rc) const
  {
    return lc < rc;
  }
};

template <typename V, typename CompType>
struct CompGreater
{
  bool operator()(const V& lv, const CompType& lc,
    const V& rv, const CompType& rc) const
  {
    return lc > rc;
  }
};

// A standard Least-Recently-Used cache
template <typename K, typename V>
using LRUCache = Cache<K, V, int, RUUpdate, CompLess<V,int>>;
template <typename V>
using LRUSet = Cache<void, V, int, RUUpdate, CompLess<V,int>>;

// A standard Most-Recently-Used cache
template <typename K, typename V>
using MRUCache = Cache<K, V, int, RUUpdate, CompGreater<V,int>>;
template <typename V>
using MRUSet = Cache<void, V, int, RUUpdate, CompGreater<V,int>>;

// A standard Least-Frequently-Used cache
template <typename K, typename V>
using LFUCache = Cache<K, V, int, FUUpdate, CompLess<V,int>>;
template <typename V>
using LFUSet = Cache<void, V, int, FUUpdate, CompLess<V,int>>;

// A standard Most-Frequently-Used cache
template <typename K, typename V>
using MFUCache = Cache<K, V, int, FUUpdate, CompGreater<V,int>>;
template <typename V>
using MFUSet = Cache<void, V, int, FUUpdate, CompGreater<V,int>>;

template <typename T, typename V>
void __cache_compile_test_set(V defelem)
{
  T c1(10);

  assert(c1.empty()); assert(c1.size() == 0);
  auto itr = c1.insert(defelem);
  assert(itr.second); assert(*itr.first == defelem); assert(c1.size() == 1);
  assert(c1.count(defelem) == 1);
  auto itr2 = c1.find(defelem);
  assert(itr2 != c1.end()); assert(*itr2 == defelem);
  assert(*c1.begin() == defelem);
  auto firstelem = c1.pop();
  assert(firstelem == defelem); assert(c1.size() == 0);
  assert(c1.find(defelem) == c1.end());
  auto itr3 = c1.emplace(defelem);
  assert(itr3.second); assert(*itr3.first == defelem);
  c1.erase(c1.find(defelem));
  assert(c1.size() == 0);
  c1.emplace(defelem);
  assert(c1.size() == 1); assert(c1.erase(defelem) == 1);
  assert(c1.size() == 0);
}
template <typename T, typename K, typename V>
void __cache_compile_test_map(K defkey, V defelem)
{
  T c1(10);

  assert(c1.empty()); assert(c1.size() == 0);
  auto itr = c1.insert(make_pair(defkey, defelem));
  assert(itr.second); assert(itr.first->second == defelem);
  assert(c1.size() == 1); assert(c1.count(defkey) == 1);
  auto itr2 = c1.find(defkey);
  assert(itr2 != c1.end()); assert(itr2->second == defelem);
  assert(c1.at(defkey) == defelem); assert(c1[defkey] == defelem);
  assert(c1.begin()->second == defelem);
  auto firstelem = c1.pop();
  assert(firstelem.first == defkey); assert(firstelem.second == defelem);
  assert(c1.size() == 0); assert(c1.find(defkey) == c1.end());
  auto itr3 = c1.emplace(defkey, defelem);
  assert(c1.size() == 1); assert(itr3.second);
  assert(itr3.first->second == defelem);
  c1.erase(c1.find(defkey)); assert(c1.size() == 0);
  c1.emplace(defkey, defelem); assert(c1.size() == 1);
  assert(c1.erase(defkey) == 1);
  assert(c1.size() == 0);
}

void __cache_compile_test()
{
  __cache_compile_test_set<LRCSet<long>,long>(5);
  __cache_compile_test_map<LRCCache<bool,long>,long,long>(false, 5);
  __cache_compile_test_set<LRUSet<long>,long>(5);
  __cache_compile_test_map<LRUCache<bool,long>,long,long>(false, 5);
  __cache_compile_test_set<LFUSet<long>,long>(5);
  __cache_compile_test_map<LFUCache<bool,long>,long,long>(false, 5);
}

#endif
