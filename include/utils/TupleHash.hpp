#ifndef TUPLEHASH__HPP__
#define TUPLEHASH__HPP__

#include <boost/container_hash/hash.hpp>

namespace std
{
template <size_t S, typename... T>
struct tuphash
{
  typedef typename std::tuple_element<S-1,std::tuple<T...>>::type stype;
  inline size_t operator()(const std::tuple<T...>& tup)
  {
    std::size_t firsthash = std::hash<stype>()(std::get<S-1>(tup));
    boost::hash_combine(firsthash, tuphash<S-1,T...>()(tup));
    return firsthash;
  }
};
template <typename... T>
struct tuphash<0,T...>
{
  typedef typename std::tuple_element<0,std::tuple<T...>>::type stype;
  inline size_t operator()(const std::tuple<T...>& tup)
  {
    return std::hash<stype>()(std::get<0>(tup));
  }
};

template <typename... T>
struct hash<std::tuple<T...>>
{
  size_t operator()(const std::tuple<T...>& tup) const
  {
    static const size_t tsize = sizeof...(T);
    return tuphash<tsize,T...>()(tup);
  }
};
}
#endif
