#ifndef PTSIMPL__HPP__
#define PTSIMPL__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include <vector>
#include <algorithm>
#include <boost/logic/tribool.hpp>

namespace ufo
{
using namespace std;
using namespace boost;

template <typename T, typename UnaryPredicate>
bool any_of(const T& container, UnaryPredicate pred)
{ return any_of(begin(container), end(container), pred); }

template <typename T, typename UnaryPredicate>
bool all_of(const T& container, UnaryPredicate pred)
{ return all_of(begin(container), end(container), pred); }

typedef function<boost::tribool(Expr)> IsTrueFalseFn;

class PTSimpl {
  Expr ezero, eone, enegone;
  ParseTree ptzero, ptone, ptnegone, pttrue, ptfalse;
  public:

  explicit PTSimpl(ExprFactory& efac)
  {
    ezero = mkTerm(mpz_class(0), efac);
    eone = mkTerm(mpz_class(1), efac);
    enegone = mkTerm(mpz_class(-1), efac);
    ptzero = ezero;
    ptone = eone;
    ptnegone = enegone;
    ptfalse = mk<FALSE>(efac);
    pttrue = mk<TRUE>(efac);
  }

// Returns a new ParseTree if pt can be rewritten, otherwise returns `NULL`.
// `isTrueFalse` is a function taking an Expr and returning `true` if the
//   Expr is a tautology, `indeterminate` if Expr is sometimes true (SAT),
//   and `false` if Expr is a contradiction.
// E.g. `rewritePT(false & x)` will return `false`,
//      `rewritePT(true & x)` will return `NULL`.
  ParseTree rewritePT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    Expr optype = typeOf(pt.data());
    if (is_bvop(pt.data()))
      return std::move(rewriteBVPT(pt, isTrueFalse));
    else if (isOpX<BOOL_TY>(optype))
      return std::move(rewriteBoolPT(pt, isTrueFalse));
    else if (isOpX<INT_TY>(optype))
      return std::move(rewriteIntPT(pt, isTrueFalse));

    return NULL;
  }

  // Returns a list of elements from `args` which should be removed.
  // Return is guaranteed to be in sorted order.
  // `isTrueFalse` is a function taking an Expr and returning `true` if the
  //   Expr is a tautology, `indeterminate` if Expr is sometimes true (SAT),
  //   and `false` if Expr is a contradiction.
  // E.g. `prunePT(AND, {true, x, true})` will return `{0, 2}`.
  vector<int> prunePT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    vector<int> empty;
    Expr optype = typeOf(oper);
    if (isOpX<ITE>(oper))
    {
      assert(args.size() == 3);
      tribool firstTF = isTrueFalse(args[0].toExpr());
      if (firstTF)
        return vector<int>{0, 2};
      else if (!firstTF)
        return vector<int>{0, 1};
    }
    if (is_bvop(oper))
      return std::move(pruneBVPT(oper, args, isTrueFalse));
    else if (isOpX<BOOL_TY>(optype))
      return std::move(pruneBoolPT(oper, args, isTrueFalse));
    else if (isOpX<INT_TY>(optype))
      return std::move(pruneIntPT(oper, args, isTrueFalse));

    return std::move(empty);
  }

  private:

  ParseTree rewriteBoolPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    Expr oper = pt.data();
    if (!oper || pt.children().size() == 0)
      return NULL;
    if (isOpX<NEG>(oper))
    {
      assert(pt.children().size() == 1);
      tribool isTF = isTrueFalse(pt.children()[0].toExpr());
      if (!isTF) return pttrue;
      else if (isTF) return ptfalse;
    }
    else if (isOpX<AND>(oper))
    {
      bool anyFalse = false, allTrue = true;
      for (const auto& child : pt.children())
      {
        tribool isTF = isTrueFalse(child.toExpr());
        if (!isTF)
          anyFalse = true;
        if (!isTF || indeterminate(isTF))
          allTrue = false;
      }
      if (anyFalse) return ptfalse;
      else if (allTrue) return pttrue;
    }
    else if (isOpX<OR>(oper))
    {
      bool anyTrue = false, allFalse = true;
      for (const auto& child : pt.children())
      {
        tribool isTF = isTrueFalse(child.toExpr());
        if (isTF)
          anyTrue = true;
        if (isTF || indeterminate(isTF))
          allFalse = false;
      }
      if (anyTrue) return pttrue;
      else if (allFalse) return ptfalse;
    }
    else if (isOpX<IMPL>(oper))
    {
      assert(pt.children().size() == 2);
      tribool leftTF = isTrueFalse(pt.children()[0].toExpr()),
              rightTF = isTrueFalse(pt.children()[1].toExpr());

      if (leftTF && !rightTF) return ptfalse;
      else if (!leftTF || rightTF) return pttrue;
    }
    else if (isOpX<EQ>(oper))
    {
      const ParseTree& first = pt.children()[0];
      for (const auto& child : pt.children())
        if (child != first) return NULL; // i.e. "we don't know"
      return pttrue; // All children == first
    }
    else if (isOpX<NEQ>(oper))
    {
      unordered_set<Expr> seen;
      for (const auto& child : pt.children())
        if (!seen.insert(child.toExpr()).second) return ptfalse; // two of child
      return NULL; // i.e. "we don't know"
    }
    else if (isOpX<FORALL>(oper) || isOpX<EXISTS>(oper))
    {
      tribool isTF = isTrueFalse(pt.children()[0].toExpr());
      if (isTF)       return pttrue;
      else if (!isTF) return ptfalse;
      else            return NULL;
    }
    if (pt.children().size() != 2)
      return NULL;
    Expr left = pt.children()[0].toSortedExpr(),
         right = pt.children()[1].toSortedExpr();

    if (isNum(left) && isNum(right)) // Evaluate e.g. 0 < 1
      return evaluateCmpConsts(oper,
        getTerm<mpz_class>(left), getTerm<mpz_class>(right)) ? pttrue : ptfalse;

    if (isOpX<LT>(oper) && left == right)
      return ptfalse;
    else if (isOpX<LEQ>(oper) && left == right)
      return pttrue;
    else if (isOpX<GT>(oper) && left == right)
      return ptfalse;
    else if (isOpX<GEQ>(oper) && left == right)
      return pttrue;

    return NULL;
  }

  ParseTree rewriteIntPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    Expr oper = pt.data();
    if (!oper || pt.children().size() < 1)
      return NULL;
    Expr left = pt.children()[0].toSortedExpr();
    if (isNum(left) && pt.children().size() == 1)
      return simplifyArithm(pt.toExpr(), true, true);

    if (pt.children().size() != 2)
      return NULL;

    Expr right = pt.children()[1].toSortedExpr();

    if (isNum(left) && isNum(right)) // Evaluate e.g. 0 + 1
      return simplifyArithm(pt.toExpr(), true, true);

    if (isOpX<PLUS>(oper) && left == additiveInverse(right))
      return ptzero;
    else if (isOpX<MINUS>(oper))
    {
      if (left == right) return ptzero;
      else if (left == ezero) return additiveInverse(right);
    }
    else if (isOpX<MULT>(oper))
    {
      if (left == enegone) return additiveInverse(right);
      else if (right == enegone) return additiveInverse(left);
    }
    else if ((isOpX<DIV>(oper) || isOpX<IDIV>(oper)) && left == right)
      return ptone;

    return NULL;
  }

  ParseTree rewriteBVPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    if (!pt.data() || pt.children().size() < 1)
      return NULL;
    Expr oper = pt.data(), sort = typeOf(pt.data());
    mpz_class allones;
    mpz_pow_ui(allones.get_mpz_t(), mpz_class(2).get_mpz_t(), bv::width(sort));
    Expr bvzero(bv::bvnum(mpz_class(0), sort)),
         bvone(bv::bvnum(mpz_class(1), sort)),
         bvallones(bv::bvnum(allones, sort));
    ParseTree ptbvzero(bvzero), ptbvone(bvone), ptbvallones(bvallones);
    Expr left = pt.children()[0].toSortedExpr();
    /*if (isNum(left) && pt.children().size() == 1)
      return evaluateBVOp(pt.toExpr());*/
    Expr right = pt.children()[1].toSortedExpr();

    /*if (isNum(left) && isNum(right)) // Evaluate e.g. 0 + 1
      return evaluateBVOp(pt.toExpr());*/

    if (isOpX<BXOR>(oper))
    {
      if (left == right) return ptbvzero;
      else if (left == bvallones) return bvAdditiveInverse(right);
      else if (right == bvallones) return bvAdditiveInverse(left);
    }
    else if (isOpX<BNAND>(oper) && (left == bvzero || right == bvzero))
      return ptbvallones;
    else if (isOpX<BNOR>(oper) && (left == bvallones || right == bvallones))
      return ptbvzero;
    else if (isOpX<BXNOR>(oper) && (left == right))
      return ptbvallones;

    else if ((isOpX<BULT>(oper) || isOpX<BSLT>(oper)) && left == right)
      return ptfalse;
    else if ((isOpX<BULE>(oper) || isOpX<BSLE>(oper)) && left == right)
      return pttrue;
    else if ((isOpX<BUGT>(oper) || isOpX<BSGT>(oper)) && left == right)
      return ptfalse;
    else if ((isOpX<BUGE>(oper) || isOpX<BSGE>(oper)) && left == right)
      return pttrue;
    else if (isOpX<BUGE>(oper) && right == bvzero)
      return pttrue;
    else if (isOpX<BULT>(oper) && right == bvzero)
      return ptfalse;

    else if (isOpX<BADD>(oper) && left == bvAdditiveInverse(right))
      return ptbvzero;
    else if (isOpX<BSUB>(oper))
    {
      if (left == right) return ptbvzero;
      else if (left == bvzero) return bvAdditiveInverse(right);
    }
    else if (isOpX<BMUL>(oper))
    {
      if (left == bvallones) return bvAdditiveInverse(right);
      else if (right == bvallones) return bvAdditiveInverse(left);
    }
    else if ((isOpX<BUDIV>(oper) || isOpX<BSDIV>(oper)) && left == right)
      return ptbvone;

    return NULL;
  }

  vector<int> pruneBoolPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    vector<int> empty;
    if (!oper || args.size() == 0)
      return std::move(empty);
    if (isOpX<AND>(oper) || isOpX<OR>(oper))
    {
      // Prune `true` and duplicates from AND
      // Prune `false` and duplicates from OR
      bool isand = isOpX<AND>(oper);
      vector<int> ret;
      unordered_set<Expr> seen;
      for (int i = 0; i < args.size(); ++i)
        if ((isand == isTrueFalse(args[i].toExpr())) || !seen.insert(args[i].toExpr()).second)
          ret.push_back(i);
      if (ret.size() == args.size())
        ret.erase(ret.begin());
      return std::move(ret);
    }
    else if (isOpX<IMPL>(oper))
    {
      assert(args.size() == 2);
      if (isTrueFalse(args[0].toExpr()))
        return vector<int>{0};
    }
    /*else if (isOpX<EQ>(oper))
    {
      if (args.size() == 2) // Optimization for common case
        return std::move(empty);

      // Otherwise, prune known equivalent expressions
      unordered_set<Expr> found;
      vector<int> ret;
      for (int i = 0; i < args.size(); ++i)
        if (!found.insert(args[i]).second)
          ret.push_back(i);
      return std::move(ret);
    }*/
    return std::move(empty);
  }

  vector<int> pruneIntPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    vector<int> empty;
    if (args.size() != 2)
      return std::move(empty);
    Expr left = args[0].toSortedExpr(), right = args[1].toSortedExpr();
    vector<int> pruneright({1}), pruneleft({0});
    if (isOpX<PLUS>(oper))
    {
      if (left == ezero) return std::move(pruneleft);
      else if (right == ezero) return std::move(pruneright);
    }
    else if (isOpX<MINUS>(oper))
    {
      if (right == ezero) return std::move(pruneright);
    }
    else if (isOpX<MULT>(oper))
    {
      if (left == eone) return std::move(pruneleft);
      else if (right == eone) return std::move(pruneright);
      else if (left == ezero) return std::move(pruneright);
      else if (right == ezero) return std::move(pruneleft);
    }
    else if (isOpX<DIV>(oper) || isOpX<IDIV>(oper))
    {
      if (right == eone) return std::move(pruneright);
      else if (left == ezero) return std::move(pruneright);
    }
    else if (isOpX<MOD>(oper))
    {
      if (left == right) return std::move(pruneleft);
      else if (right == eone) return std::move(pruneleft);
    }

    return std::move(empty);
  }

  vector<int> pruneBVPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    vector<int> empty;
    if (args.size() != 2)
      return std::move(empty);
    Expr left = args[0].toSortedExpr(), right = args[1].toSortedExpr();
    vector<int> pruneright({1}), pruneleft({0});
    Expr sort = typeOf(oper);
    Expr bvzero(bv::bvnum(mpz_class(0), sort)),
         bvone(bv::bvnum(mpz_class(1), sort)),
         bvnegone(bv::bvnum(mpz_class(-1), sort));

    if (isOpX<BAND>(oper))
    {
      if (left == bvzero) return std::move(pruneright);
      else if (right == bvzero) return std::move(pruneleft);
      else if (left == bvnegone) return std::move(pruneleft);
      else if (right == bvnegone) return std::move(pruneright);
    }
    else if (isOpX<BOR>(oper))
    {
      if (left == bvzero) return std::move(pruneleft);
      else if (right == bvzero) return std::move(pruneright);
      else if (left == bvnegone) return std::move(pruneright);
      else if (right == bvnegone) return std::move(pruneleft);
    }
    else if (isOpX<BXOR>(oper))
    {
      if (left == bvzero) return std::move(pruneleft);
      else if (right == bvzero) return std::move(pruneright);
    }

    else if (isOpX<BADD>(oper))
    {
      if (left == bvzero) return std::move(pruneleft);
      else if (right == bvzero) return std::move(pruneright);
    }
    else if (isOpX<BSUB>(oper))
    {
      if (right == bvzero) return std::move(pruneright);
    }
    else if (isOpX<BMUL>(oper))
    {
      if (left == bvzero) return std::move(pruneright);
      else if (right == bvzero) return std::move(pruneleft);
    }
    else if (isOpX<BUDIV>(oper) || isOpX<BSDIV>(oper))
    {
      if (left == bvone || left == bvzero) return std::move(pruneright);
      else if (right == bvone) return std::move(pruneright);
    }
    else if (isOpX<BUREM>(oper) || isOpX<BSREM>(oper) || isOpX<BSMOD>(oper))
    {
      if (left == right) return std::move(pruneleft);
      else if (right == bvone) return std::move(pruneleft);
    }

    else if (isOpX<BSHL>(oper) || isOpX<BLSHR>(oper) || isOpX<BASHR>(oper))
      if (right == bvzero) return std::move(pruneright);

    return std::move(empty);
  }
};

}

#endif
