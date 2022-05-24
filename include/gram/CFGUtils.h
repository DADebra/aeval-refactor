#ifndef CFGUTILS__H__
#define CFGUTILS__H__

#include "gram/Grammar.h"
#include "gram/TravParams.hpp"

namespace ufo
{

const char* ANY_INV = "ANY_INV";
// The maximum arity of 'either' functions we write.
const int NUMEITHERS = 100;

class CFGUtils
{
  static unordered_map<pair<Expr,VarType>,Expr> varsNtNameCache;
  static unordered_map<Expr,Expr> constsNtNameCache;

  public:

  // To uppercase, translate e.g. (Array Int Int) to $ARRAY_INT_INT$
  static string sortName(Expr sort);

  static Expr varsNtName(Expr sort, VarType type);
  static Expr constsNtName(Expr sort);

  static void noNtDefError(NT nt, NT root);
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
