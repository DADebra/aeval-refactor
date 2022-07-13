#ifndef PAIRHASH__HPP__
#define PAIRHASH__HPP__

namespace std
{
template <typename S, typename T>
struct hash<std::pair<S,T>>
{
  size_t operator()(const std::pair<S,T>& pr) const
  {
    return std::hash<S>()(pr.first) * std::hash<T>()(pr.second);
  }
};
}
#endif
