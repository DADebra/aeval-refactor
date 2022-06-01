#ifndef CFGUTILS__H__
#define CFGUTILS__H__

#include <unordered_map>
#include <utility>
#include <string>

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
  static unordered_map<pair<Expr,VarType>,Expr>* varsNtNameCache;
  static unordered_map<Expr,Expr>* constsNtNameCache;
  static int refcnt;

  void increment()
  {
    if (refcnt == 0)
    {
      varsNtNameCache = new unordered_map<pair<Expr,VarType>,Expr>();
      constsNtNameCache = new ExprUMap();
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

  static Expr varsNtName(Expr sort, VarType type);
  static Expr constsNtName(Expr sort);

  static void noNtDefError(NT nt, NT root);
  static bool isEither(const Expr&);
  static Grammar parseGramFile(string, string, EZ3&, ExprFactory&, int,
    const VarMap&, const VarMap&);
  static ExprUSet getQVars(const Grammar&);
  static string toSyGuS(Grammar&, EZ3&);

  static TPMethod strtogenmethod(const char* methodstr);
  static TPDir strtotravdir(const char* str);
  static TPOrder strtotravord(const char* str);
  static TPType strtotravtype(const char* str);
  static TPPrio strtotravprio(const char* str);
};

}

#endif
