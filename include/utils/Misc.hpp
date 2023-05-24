#ifndef __MISC__HPP__
#define __MISC__HPP__

#include <functional>

template <typename T, typename UnaryPredicate>
bool any_of(const T& container, UnaryPredicate pred)
{ return any_of(begin(container), end(container), pred); }

template <typename T, typename UnaryPredicate>
bool all_of(const T& container, UnaryPredicate pred)
{ return all_of(begin(container), end(container), pred); }

// Like std::pair, but can be interpreted as the first item
template <typename T, typename Extra, bool ExtraHash=true>
struct WithExtra
{
  T obj;
  Extra extra;
  WithExtra() {}
  WithExtra(T _obj, Extra _extra) : obj(_obj), extra(_extra) {}

  operator T() const { return obj; }

  bool operator==(const WithExtra<T,Extra,ExtraHash> &oth) const
  { return obj == oth.obj && extra == oth.extra; }
  bool operator!=(const WithExtra<T,Extra,ExtraHash> &oth) const
  { return !(*this == oth); }
};

namespace std
{
template <typename T, typename Extra>
struct hash<WithExtra<T,Extra,true>>
{
  size_t operator()(const WithExtra<T,Extra,true>& we) const
  {
    auto hash = std::hash<T>()(we.obj);
    boost::hash_combine(hash, std::hash<Extra>()(we.extra));
    return hash;
  }
};

template <typename T, typename Extra>
struct hash<WithExtra<T,Extra,false>>
{
  size_t operator()(const WithExtra<T,Extra,false>& we) const
  {
    return std::hash<T>()(we.obj);
  }
};
}

#endif
