#ifndef SETHASH__HPP__
#define SETHASH__HPP__

#include <boost/container_hash/hash.hpp>

namespace std
{
template <typename T, typename Comp, typename Alloc>
struct hash<set<T,Comp,Alloc>>
{
  size_t operator()(const set<T,Comp,Alloc>& obj) const
  {
    auto itr = obj.begin();
    auto end = obj.end();
    auto hashT = hash<T>();
    if (itr == end)
      return hashT(T());
    size_t outhash = hashT(*itr);
    ++itr;
    for (; itr != end; ++itr)
      boost::hash_combine(outhash, hashT(*itr));
    return outhash;
  }
};
}
#endif
