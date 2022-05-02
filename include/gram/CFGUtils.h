#ifndef CFGUTILS__H__
#define CFGUTILS__H__

#include "gram/Grammar.h"
#include "gram/TravParams.hpp"

namespace ufo
{

const char* ANY_INV = "ANY_INV";
const char* INT_CONSTS = "INT_CONSTS";
// The maximum arity of 'either' functions we write.
const int NUMEITHERS = 100;

class CFGUtils
{
  public:

  static bool isEither(const Expr&);
  static bool isRecursive(const Expr&, const Expr&);
  static Grammar parseGramFile(string, string, EZ3&, ExprFactory&, int,
    const VarMap&, const VarMap&);
  static ExprUSet getQVars(const Grammar&);
  static string toSyGuS(Grammar&, EZ3&);
  static string findGram(vector<string>&, Expr, bool useany = false);
  static TPMethod strtogenmethod(const char* methodstr);
  static TPDir strtotravdir(const char* str);
  static TPOrder strtotravord(const char* str);
  static TPType strtotravtype(const char* str);
  static TPPrio strtotravprio(const char* str);
};

}

#endif
