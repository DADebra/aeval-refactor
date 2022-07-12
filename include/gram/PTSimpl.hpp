#ifndef PTSIMPL__HPP__
#define PTSIMPL__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include <vector>
#include <algorithm>
#include <boost/logic/tribool.hpp>

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

namespace ufo
{
using namespace std;
using namespace boost;

typedef function<boost::tribool(Expr)> IsTrueFalseFn;
typedef std::tuple<std::vector<int>,std::vector<int>,ParseTree> PruneRetType;

class PTSimpl {
  Expr ezero, eone, enegone;
  ParseTree ptzero, ptone, ptnegone, pttrue, ptfalse;
  unordered_map<Expr,Expr> _bvzero, _bvone, _bvallones; // K: Sort, V: Term
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
    if (!pt || !pt.data() || pt.children().size() == 0)
      return NULL;
    if (isOpX<ITE>(pt.data()))
    {
      assert(pt.children().size() == 3);
      tribool firstTF = isTrueFalse(pt.children()[0].toSortedExpr());
      if (firstTF)
        return pt.children()[1];
      else if (!firstTF)
        return pt.children()[2];
    }
    Expr optype = typeOf(pt.data());
    if (is_bvop(pt.data()))
      return std::move(rewriteBVPT(pt, isTrueFalse));
    else if (isOpX<BOOL_TY>(optype))
      return std::move(rewriteBoolPT(pt, isTrueFalse));
    else if (isOpX<INT_TY>(optype))
      return std::move(rewriteIntPT(pt, isTrueFalse));

    return NULL;
  }

  // Returns 3 things:
  // - A list of indices (in `args`) which are causing a short-circuit
  //     evaluation (empty if nothing to prune).
  // - A list of indices which will permanently be useless,
  //     i.e. regardless of what value they hold the resultant expression will
  //     be unchanged (empty if first ret value if empty)
  // - The resultant ParseTree (which might not be
  //     equivalent to `ParseTree(oper, args - 1st return)`), NULL if 1st return
  //     is empty.
  // Returns are guaranteed to be in sorted order.
  // `isTrueFalse` is a function taking an Expr and returning `true` if the
  //   Expr is a tautology, `indeterminate` if Expr is sometimes true (SAT),
  //   and `false` if Expr is a contradiction.
  // E.g. `prunePT(AND, {false, x, true}, 1)` will return `{1, 2}`.
  PruneRetType prunePT(Expr oper, const vector<ParseTree> &args,
    const IsTrueFalseFn& isTrueFalse)
  {
    PruneRetType empty;
    if (!oper || args.empty())
      return std::move(empty);
    Expr optype = typeOf(oper);
    if (isOpX<ITE>(oper))
    {
      assert(args.size() == 3);
      tribool firstTF = isTrueFalse(args[0].toSortedExpr());
      if (firstTF)
        return make_tuple(vector<int>{0}, vector<int>{2}, args[1]);
      else if (!firstTF)
        return make_tuple(vector<int>{0}, vector<int>{1}, args[2]);
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

  Expr bvzero(Expr sort)
  {
    auto itr = _bvzero.find(sort);
    if (itr == _bvzero.end())
      itr = _bvzero.emplace(sort, bv::bvnum(mpz_class(0), sort)).first;
    return itr->second;
  }

  Expr bvone(Expr sort)
  {
    auto itr = _bvone.find(sort);
    if (itr == _bvone.end())
      itr = _bvone.emplace(sort, bv::bvnum(mpz_class(1), sort)).first;
    return itr->second;
  }

  Expr bvallones(Expr sort)
  {
    auto itr = _bvallones.find(sort);
    if (itr == _bvallones.end())
    {
      mpz_class allones;
      mpz_pow_ui(allones.get_mpz_t(), mpz_class(2).get_mpz_t(), bv::width(sort));
      itr = _bvallones.emplace(sort, bv::bvnum(allones, sort)).first;
    }
    return itr->second;
  }

  ParseTree rewriteBoolPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    Expr oper = pt.data();
    if (isOpX<NEG>(oper))
    {
      assert(pt.children().size() == 1);
      tribool isTF = isTrueFalse(pt.children()[0].toSortedExpr());
      if (!isTF) return pttrue;
      else if (isTF) return ptfalse;
    }
    else if (isOpX<AND>(oper) || isOpX<OR>(oper))
    {
      // Prune `true` and duplicates from AND
      // Prune `false` and duplicates from OR
      bool isand = isOpX<AND>(oper);
      vector<ParseTree> ret;
      unordered_set<Expr> seen;
      for (int i = 0; i < pt.children().size(); ++i)
      {
        Expr child = pt.children()[i].toSortedExpr();
        if ((isand == isTrueFalse(child)) || !seen.insert(child).second)
          continue;
        else
          ret.push_back(pt.children()[i]);
      }
      if (ret.size() == 0)
        ret.push_back(pt.children()[0]);
      if (ret.size() == 1)
        return ret[0];
      return ParseTree(oper, std::move(ret), pt.isNt());
    }
    else if (isOpX<IMPL>(oper))
    {
      assert(pt.children().size() == 2);
      tribool leftTF = isTrueFalse(pt.children()[0].toSortedExpr()),
              rightTF = isTrueFalse(pt.children()[1].toSortedExpr());

      if (leftTF && !rightTF) return ptfalse;
      else if (!leftTF || rightTF) return pttrue;
      else if (leftTF) return pt.children()[1];
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
        if (!seen.insert(child.toSortedExpr()).second) return ptfalse; // two of child
      return NULL; // i.e. "we don't know"
    }
    else if (isOpX<FORALL>(oper) || isOpX<EXISTS>(oper))
    {
      tribool isTF = isTrueFalse(pt.children()[0].toSortedExpr());
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

    tribool isTF = isTrueFalse(pt.toSortedExpr());
    if (isTF) return pttrue;
    else if (!isTF) return ptfalse;

    return NULL;
  }

  ParseTree negPT(const ParseTree& pt)
  {
    if (isOpX<MPZ>(pt.data()))
      return mkTerm<mpz_class>(-getTerm<mpz_class>(pt.data()), pt.data()->efac());
    assert(pt.children().size() == 1);
    return ParseTree(pt.data(), negPT(pt.children()[0]), pt.isNt());
  }

  ParseTree rewriteIntPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    Expr oper = pt.data();
    if (!oper || pt.children().size() < 1)
      return NULL;
    const ParseTree &ptleft = pt.children()[0];
    Expr left = ptleft.toSortedExpr();
    if (isNum(left) && pt.children().size() == 1)
      return simplifyArithm(pt.toSortedExpr(), true, true);

    if (pt.children().size() != 2)
      return NULL;

    const ParseTree &ptright = pt.children()[1];
    Expr right = ptright.toSortedExpr();

    if (isNum(left) && isNum(right)) // Evaluate e.g. 0 + 1
      return simplifyArithm(pt.toSortedExpr(), true, true);

    if (isOpX<PLUS>(oper))
    {
      if (left == ezero) return ptright;
      else if (right == ezero) return ptleft;
      else if (left == additiveInverse(right)) return ptzero;
    }
    else if (isOpX<MINUS>(oper))
    {
      if (left == right) return ptzero;
      else if (left == ezero) return additiveInverse(right);
      else if (right == ezero) return ptleft;
    }
    else if (isOpX<MULT>(oper))
    {
      if (left == eone) return ptright;
      else if (right == eone) return ptleft;
      else if (left == enegone) return additiveInverse(right);
      else if (right == enegone) return additiveInverse(left);
    }
    else if (isOpX<DIV>(oper) || isOpX<IDIV>(oper))
    {
      if (right == eone) return ptleft;
    }
    else if (isOpX<MOD>(oper))
    {
      if (left == right) return ptleft;
      if (isOpX<MPZ>(right))
      {
        mpz_class div = getTerm<mpz_class>(right);
        if (div < 0)
          return ParseTree(oper, vector<ParseTree>{ptleft, negPT(ptright)},
            pt.isNt());
      }
    }
    else if ((isOpX<DIV>(oper) || isOpX<IDIV>(oper)) && left == right)
      return ptone;

    return NULL;
  }

  inline tribool bvIsTrueFalse(Expr sort, Expr e)
  {
    if (e == bvallones(sort))
      return true;
    else if (e == bvzero(sort))
      return false;
    else
      return indeterminate;
  }

  ParseTree rewriteBVPT(const ParseTree& pt, const IsTrueFalseFn& isTrueFalse)
  {
    if (!pt.data() || pt.children().size() < 1)
      return NULL;
    Expr oper = pt.data(), sort = typeOf(pt.data());
    Expr lbvzero(bvzero(sort)), lbvone(bvone(sort)), lbvallones(bvallones(sort));
    ParseTree ptbvzero(lbvzero), ptbvone(lbvone), ptbvallones(lbvallones);
    const ParseTree &ptleft = pt.children()[0];
    Expr left = ptleft.toSortedExpr();
    /*if (isNum(left) && pt.children().size() == 1)
      return evaluateBVOp(pt.toSortedExpr());*/
    const ParseTree &ptright = pt.children()[1];
    Expr right = ptright.toSortedExpr();

    /*if (isNum(left) && isNum(right)) // Evaluate e.g. 0 + 1
      return evaluateBVOp(pt.toSortedExpr());*/

    if (isOpX<BAND>(oper) || isOpX<BOR>(oper) ||
        isOpX<BNAND>(oper) || isOpX<BNOR>(oper))
    {
      bool isand = isOpX<BAND>(oper) || isOpX<BNAND>(oper);
      vector<ParseTree> ret;
      unordered_set<Expr> seen;
      for (int i = 0; i < pt.children().size(); ++i)
      {
        Expr child = pt.children()[i].toSortedExpr();
        if ((isand == bvIsTrueFalse(sort, child)) || !seen.insert(child).second)
          continue;
        else
          ret.push_back(pt.children()[i]);
      }
      if (ret.size() == 0)
        ret.push_back(pt.children()[0]);
      if (ret.size() == 1)
        return ret[0];
      return ParseTree(oper, std::move(ret), pt.isNt());
    }
    else if (isOpX<BXOR>(oper))
    {
      if (left == lbvzero) return ptright;
      else if (right == lbvzero) return ptleft;
    }

    else if (isOpX<BADD>(oper))
    {
      if (left == lbvzero) return ptright;
      else if (right == lbvzero) return ptleft;
      else if (left == bvAdditiveInverse(right))
        return ptbvzero;
    }
    else if (isOpX<BSUB>(oper))
    {
      if (right == lbvzero) return ptleft;
      else if (left == right) return ptbvzero;
      else if (left == lbvzero) return bvAdditiveInverse(right);
    }
    else if (isOpX<BMUL>(oper))
    {
      if (left == lbvone) return ptright;
      else if (right == lbvone) return ptleft;
      // Because all 1's == -1
      else if (left == lbvallones) return bvAdditiveInverse(right);
      else if (right == lbvallones) return bvAdditiveInverse(left);
    }
    else if (isOpX<BUDIV>(oper) || isOpX<BSDIV>(oper))
    {
      if (right == lbvone) return ptleft;
      else if (left == right)
        return ptbvone;
    }
    else if (isOpX<BUREM>(oper) || isOpX<BSREM>(oper) || isOpX<BSMOD>(oper))
    {
      if (left == right) return ptleft;
    }

    else if (isOpX<BSHL>(oper) || isOpX<BLSHR>(oper) || isOpX<BASHR>(oper))
    {
      if (right == lbvzero) return ptleft;
    }
    if (isOpX<BXOR>(oper))
    {
      if (left == right) return ptbvzero;
      else if (left == lbvallones) return bvAdditiveInverse(right);
      else if (right == lbvallones) return bvAdditiveInverse(left);
    }

    else if ((isOpX<BULT>(oper) || isOpX<BSLT>(oper)) && left == right)
      return ptfalse;
    else if ((isOpX<BULE>(oper) || isOpX<BSLE>(oper)) && left == right)
      return pttrue;
    else if ((isOpX<BUGT>(oper) || isOpX<BSGT>(oper)) && left == right)
      return ptfalse;
    else if ((isOpX<BUGE>(oper) || isOpX<BSGE>(oper)) && left == right)
      return pttrue;
    else if (isOpX<BUGE>(oper) && right == lbvzero)
      return pttrue;
    else if (isOpX<BULT>(oper) && right == lbvzero)
      return ptfalse;

    return NULL;
  }

  PruneRetType pruneBoolPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    PruneRetType empty;
    if (!oper || args.size() == 0)
      return std::move(empty);
    if (isOpX<AND>(oper) || isOpX<OR>(oper))
    {
      bool hasShortCircuit = false, isand = isOpX<AND>(oper);
      vector<int> culprits, ret;
      ParseTree ret2;
      for (int i = 0; i < args.size(); ++i)
      {
        tribool isTF = isTrueFalse(args[i].toSortedExpr());
        if (isand == !isTF)
        {
          ret2 = isand ? ptfalse : pttrue;
          hasShortCircuit = true;
          culprits.push_back(i);
        }
        else
          ret.push_back(i);
      }
      if (hasShortCircuit)
        return make_tuple(std::move(culprits), std::move(ret), std::move(ret2));
    }
    else if (isOpX<IMPL>(oper))
    {
      assert(args.size() == 2);
      if (!isTrueFalse(args[0].toSortedExpr()))
        return make_tuple(vector<int>{0}, vector<int>{1}, pttrue);
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

  PruneRetType pruneIntPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    PruneRetType empty;
    if (args.size() != 2)
      return std::move(empty);
    Expr left = args[0].toSortedExpr(), right = args[1].toSortedExpr();
    vector<int> rightind({1}), leftind({0});

    if (isOpX<MULT>(oper))
    {
      if (left == ezero)
        return make_tuple(std::move(leftind), std::move(rightind), args[0]);
      else if (right == ezero)
        return make_tuple(std::move(rightind), std::move(leftind), args[1]);
    }
    else if (isOpX<DIV>(oper) || isOpX<IDIV>(oper))
    {
      if (left == ezero || left == eone)
        return make_tuple(std::move(leftind), std::move(rightind), ptzero);
    }
    else if (isOpX<MOD>(oper))
    {
      if (left == ezero)
        return make_tuple(std::move(leftind), std::move(rightind), ptzero);
      else if (right == eone)
        return make_tuple(std::move(rightind), std::move(leftind), args[1]);
    }

    return std::move(empty);
  }

  PruneRetType pruneBVPT(Expr oper, const vector<ParseTree> &args, const IsTrueFalseFn& isTrueFalse)
  {
    PruneRetType empty;
    Expr left = args[0].toSortedExpr(), right = args[1].toSortedExpr();
    PruneRetType pruneleft(vector<int>{1}, vector<int>{0}, args[1]),
                 pruneright(vector<int>{0}, vector<int>{1}, args[2]);
    Expr sort = typeOf(oper);

    if (isOpX<BAND>(oper) || isOpX<BOR>(oper) ||
      isOpX<BNAND>(oper) || isOpX<BNOR>(oper))
    {
      bool hasShortCircuit = false,
           isand = isOpX<BAND>(oper) || isOpX<BNAND>(oper);
      vector<int> culprits, ret;
      ParseTree ret2;
      for (int i = 0; i < args.size(); ++i)
      {
        if (isand == bvIsTrueFalse(sort, args[i].toSortedExpr()))
        {
          if (isOpX<BAND>(oper) || isOpX<BNOR>(oper))
            ret2 = bvzero(sort);
          else
            ret2 = bvallones(sort);
          culprits.push_back(i);
          hasShortCircuit = true;
        }
        else
          ret.push_back(i);
      }
      if (hasShortCircuit)
        return make_tuple(std::move(culprits), std::move(ret), std::move(ret2));
      else
        return std::move(empty);
    }

    if (args.size() != 2)
      return std::move(empty);

    if (isOpX<BMUL>(oper))
    {
      if (left == bvzero(sort)) return std::move(pruneright);
      else if (right == bvzero(sort)) return std::move(pruneleft);
    }
    else if (isOpX<BUDIV>(oper) || isOpX<BSDIV>(oper))
    {
      if (left == bvone(sort) || left == bvzero(sort))
        return make_tuple(vector<int>{0}, vector<int>{1}, bvzero(sort));
    }
    else if (isOpX<BUREM>(oper) || isOpX<BSREM>(oper) || isOpX<BSMOD>(oper))
    {
      if (left == bvzero(sort))
        return make_tuple(vector<int>{0}, vector<int>{1}, bvzero(sort));
      else if (right == eone) return std::move(pruneleft);
    }

    else if (isOpX<BSHL>(oper) || isOpX<BLSHR>(oper) || isOpX<BASHR>(oper))
      if (left == bvzero(sort)) return std::move(pruneleft);

    return std::move(empty);
  }
};

}

#endif
