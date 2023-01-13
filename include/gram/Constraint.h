#ifndef CONSTRAINT__H__
#define CONSTRAINT__H__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include "utils/PairHash.hpp"

#include <boost/optional.hpp>

namespace ufo
{

typedef unordered_map<Expr,ParseTree> PtExpMap;
typedef unordered_map<pair<Expr,ParseTree>,ExprUSet> seen_type;

// A map of <Non-terminal, Set of Expansions> (see findExpansions)
typedef unordered_map<Expr,vector<ParseTree>> ExpansionsMap;

class Grammar;
class Constraint
{
  private:

  // Key: Non-terminal   Value: Set of Expr's that First expands to
  static void findExpansions(const ParseTree& pt, ExpansionsMap& outmap);

  // Returns the ParseTree (node) whose `data` field matches the given `data`
  //   argument and is a parent of `child`.
  // When two parents have the same `data` argument, picks the one
  //   closest to the root.
  // Returns NULL when no parent found.
  static ParseTree findHighestParent(Expr data, const ParseTree& child);

  static Expr stoe(Expr e);

  // <result, T=good,ind=can't eval,F=unsupported>
  static std::pair<mpz_class,tribool> evaluateArithExpr(Expr arith, const PtExpMap& expmap,
    seen_type& se);

  static tribool evaluateCmpExpr(Expr cmp, const PtExpMap& expmap,
    seen_type& seenexpans);

  int calculateRecDepth(const ExpansionsMap& expmap, Expr nt) const;

  void foreachExpans(Expr con, const ExpansionsMap& expmap,
    function<bool(const PtExpMap&)> func) const;

  bool doesSatExpr(Expr con, const ExpansionsMap& expmap) const;

  void ctor()
  {
    filter(expr, [] (Expr e) {
      return isOpX<FAPP>(e) && e->arity() == 1; },
      inserter(fapps, fapps.begin()));
      // Note that because of the internal ExprSet that dagVisit uses,
      // we don't need to purge duplicates from `fapps`.
  }

  public:

  Expr expr;
  bool any; // 'true' if a 'constraint_any'
  Grammar* gram;
  ExprVector fapps;

  static ExprUMap strcache;

  bool doesSat(const ParseTree& pt) const;

  Constraint(const Constraint& oth, Grammar* _gram) :
    expr(oth.expr), any(oth.any), gram(_gram), fapps(oth.fapps) {}
  Constraint(Constraint&& oth, Grammar* _gram) :
    expr(oth.expr), any(oth.any), gram(_gram), fapps(oth.fapps) {}
  Constraint(Expr e, bool _any, Grammar* _gram) : expr(e), any(_any),
    gram(_gram) { ctor(); }

  // Other constructors potentially memory unsafe
  // Use at own risk
};

}

#endif
