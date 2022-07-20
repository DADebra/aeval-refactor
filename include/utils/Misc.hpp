#ifndef __MISC__HPP__
#define __MISC__HPP__

#include <functional>

namespace std
{
template <typename T, typename UnaryPredicate>
bool any_of(const T& container, UnaryPredicate pred)
{ return any_of(begin(container), end(container), pred); }

template <typename T, typename UnaryPredicate>
bool all_of(const T& container, UnaryPredicate pred)
{ return all_of(begin(container), end(container), pred); }
}

#endif
