#ifndef GRAMMAR__HPP__
#define GRAMMAR__HPP__

#include <random>

#include "gram/ParseTree.hpp"

namespace ufo
{

bool Grammar::satsConstraints(const ParseTree& pt)
{
  for (const auto& con : constraints)
    if (!con.doesSat(pt))
      return false;
  return true;
}

}
#endif
