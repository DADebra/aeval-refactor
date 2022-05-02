#ifndef CONSTRAINT__H__
#define CONSTRAINT__H__

#include "gram/ParseTree.hpp"

#include <boost/optional.hpp>

namespace ufo
{

typedef unordered_map<Expr,ParseTree> PtExpMap;
typedef unordered_map<pair<Expr,ParseTree>,ExprUSet> seen_type;

// A map of <Non-terminal, Set of Expansions> (see findExpansions)
typedef unordered_map<Expr,vector<ParseTree>> ExpansionsMap;

class Constraint
{
  private:

  Expr expr;

  // Key: Non-terminal   Value: Set of Expr's that First expands to
  static void findExpansions(const ParseTree& pt, ExpansionsMap& outmap);

  // Returns the ParseTree (node) whose `data` field matches the given `data`
  //   argument and is a parent of `child`.
  // When two parents have the same `data` argument, picks the one
  //   closest to the root.
  // Returns NULL when no parent found.
  static ParseTree findHighestParent(Expr data, const ParseTree& child);

  static Expr stoe(Expr e);

  static optional<cpp_int> evaluateArithExpr(Expr arith, const PtExpMap& expmap,
    seen_type& se);

  static tribool evaluateCmpExpr(Expr cmp, const PtExpMap& expmap,
    seen_type& seenexpans);

  static bool doesSatExpr(Expr con, const ExpansionsMap& expmap,
    bool doAny, Expr origcon);

  static int calculateRecDepth(const ExpansionsMap& expmap, Expr nt);

  static void foreachExpans(Expr con, const ExpansionsMap& expmap,
    function<bool(const PtExpMap&)> func);

  public:

  static ExprUMap strcache;

  Constraint(Expr e) : expr(e) {}

  bool doesSat(const ParseTree& pt) const;
};

}

#endif
