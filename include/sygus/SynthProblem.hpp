#ifndef __SYNTHPROBLEM_HPP__
#define __SYNTHPROBLEM_HPP__

#include <string>
#include "ufo/Expr.hpp"

namespace ufo
{
using namespace std;
using namespace expr;

enum class SynthFuncType { NONE, SYNTH, INV };

class SynthFunc
{
  public:
  SynthFuncType type;
  Expr decl;

  SynthFunc(SynthFuncType _type, Expr _decl) : type(_type), decl(_decl) {}
};

class SynthProblem
{
  public:
  string logic;
  vector<SynthFunc> synthfuncs;
  vector<Expr> constraints;
};

}

#endif
