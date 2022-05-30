#ifndef PAIRHASH__HPP__
#define PAIRHASH__HPP__

#include <boost/container_hash/hash.hpp>

namespace std
{
template <typename S, typename T>
struct hash<std::pair<S,T>>
{
  size_t operator()(const std::pair<S,T>& pr) const
  {
    size_t outhash = std::hash<S>()(pr.first);
    boost::hash_combine(outhash, std::hash<T>()(pr.second));
    return outhash;
  }
};
}
#endif
