#ifndef CFGUTILS__H__
#define CFGUTILS__H__

#include <unordered_map>
#include <utility>
#include <string>
#include "deep/Horn.hpp"

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

namespace ufo
{
using namespace std;
const char* ANY_INV = "ANY_INV";
// The maximum arity of 'either' functions we write.
const int NUMEITHERS = 100;

// Not thread-safe
class CFGUtils
{
  static unordered_map<Expr,Expr>* varsNtNameCache;
  static unordered_map<Expr,Expr>* constsNtNameCache;
  static unordered_map<Expr,Expr>* uniqueVarDeclCache;
  static int refcnt;

  void increment()
  {
    if (refcnt == 0)
    {
      varsNtNameCache = new unordered_map<Expr,Expr>();
      constsNtNameCache = new ExprUMap();
      uniqueVarDeclCache = new ExprUMap();
    }
    ++refcnt;
  }

  void decrement()
  {
    --refcnt;
    if (refcnt == 0)
    {
      delete varsNtNameCache;
      varsNtNameCache = NULL;
      delete constsNtNameCache;
      constsNtNameCache = NULL;
      delete uniqueVarDeclCache;
      uniqueVarDeclCache = NULL;
    }
  }

  public:

  CFGUtils() { increment(); }

  ~CFGUtils() { decrement(); }

  CFGUtils(const CFGUtils& oth) { increment(); }
  CFGUtils(CFGUtils&& oth) { increment(); }

  // We've already incremented
  CFGUtils& operator=(const CFGUtils& oth) { return *this; }
  CFGUtils& operator=(CFGUtils&& oth) { return *this; }

  // To uppercase, translate e.g. (Array Int Int) to $ARRAY_INT_INT$
  static string sortName(Expr sort);

  static Expr varsNtName(Expr sort);
  static Expr constsNtName(Expr sort);
  static Expr uniqueVarDecl(Expr sort); // 1-ary, Int argument

  static void noNtDefError(NT nt, NT root);
  static bool isEither(const Expr&);
  static Grammar parseGramFile(string, string, EZ3&, ExprFactory&, int,
    const VarMap&, const VarMap&);
  static ExprUSet getQVars(const Grammar&);
  static string toSyGuS(Grammar&, EZ3&);
  static string autoGenGram(const CHCs& ruleManager);

  static TPMethod strtogenmethod(const char* str);
  static TPDir strtotravdir(const char* str);
  static TPOrder strtotravord(const char* str);
  static TPType strtotravtype(const char* str);
  static TPPrio strtotravprio(const char* str);

  static TPMethod strtogenmethod(string str) { return strtogenmethod(str.c_str()); }
  static TPDir strtotravdir(string str) { return strtotravdir(str.c_str()); }
  static TPOrder strtotravord(string str) { return strtotravord(str.c_str()); }
  static TPType strtotravtype(string str) { return strtotravtype(str.c_str()); }
  static TPPrio strtotravprio(string str) { return strtotravprio(str.c_str()); }
};

}

#endif
