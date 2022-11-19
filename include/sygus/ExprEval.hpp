#ifndef __EXPREVAL_HPP__
#define __EXPREVAL_HPP__

#include "ufo/Expr.hpp"
#include "ae/AeValSolver.hpp"

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace expr::op::bind;

namespace ufo
{

static inline Expr OpIneqs(Expr op, Expr l, Expr r)
{
  Expr lvar, rvar, lbound, rbound;
  assert(isOpX<LT>(l) || isOpX<LEQ>(l) || isOpX<GT>(l) || isOpX<GEQ>(l));
  bool islt = isOpX<LT>(l) || isOpX<LEQ>(l);
  if (islt)
    assert(isOpX<LT>(r) || isOpX<LEQ>(r));
  else
    assert(isOpX<GT>(r) || isOpX<GEQ>(r));
  lvar = l->left(); lbound = l->right();
  assert(isOpX<FAPP>(lvar));
  if (isOpX<GT>(l))
    lbound = mk<PLUS>(lbound, mkTerm(mpz_class(1), lbound->efac()));
  else if (isOpX<LT>(l))
    lbound = mk<MINUS>(lbound, mkTerm(mpz_class(1), lbound->efac()));
  rvar = r->left(); rbound = r->right();
  if (isOpX<GT>(r))
    rbound = mk<PLUS>(rbound, mkTerm(mpz_class(1), rbound->efac()));
  else if (isOpX<LT>(r))
    rbound = mk<MINUS>(rbound, mkTerm(mpz_class(1), rbound->efac()));
  assert(isOpX<FAPP>(rvar));
  assert(lvar == rvar);
  if (islt)
    return mk<LEQ>(lvar, simplifyArithm(mk(op->op(), lbound, rbound)));
  else
    return mk<GEQ>(lvar, simplifyArithm(mk(op->op(), lbound, rbound)));
}

inline Expr EvalPred(SMTUtils& u, const ExprUMap &assms, Expr toeval, Expr out)
{
  /*Expr tmpvar = mkConst(mkTerm(string("tmpqevar"), out->efac()), typeOf(out));
  ExprVector toelim, elimvars{tmpvar};
  for (const auto& hole_assm : assms)
  {
    toelim.push_back(replaceAll(hole_assm.second, out, hole_assm.first));
    elimvars.push_back(hole_assm.first);
  }
  toelim.push_back(mk<EQ>(tmpvar, toeval));
  toelim.push_back(mk<EQ>(out, tmpvar));

  Expr afterelim = eliminateQuantifiers(mknary<AND>(toelim), elimvars);*/

  if (assms.count(toeval) != 0)
    return replaceAll(assms.at(toeval), toeval, out);
  if (isOpX<FAPP>(toeval) || isLit(toeval))
    return mk<AND>(mk<GEQ>(out, toeval), mk<LEQ>(out, toeval));
  if (isOpX<ITE>(toeval))
  {
    Expr l = EvalPred(u, assms, toeval->right(), out);
    Expr r = EvalPred(u, assms, toeval->last(), out);
    if (l == r)
      return l;
    ExprVector conjs;
    for (const auto &hole_assm : assms)
      conjs.push_back(hole_assm.second);
    conjs.push_back(mk<NEG>(toeval->left()));
    if (!u.isSat(conjs))
      return l;
    conjs.back() = toeval->left();
    if (!u.isSat(conjs))
      return r;
    assert(0 && "EvalPred can't handle non-tautology ITE");
  }
  if (isOpX<PLUS>(toeval) || isOpX<MINUS>(toeval))
  {
    assert(toeval->arity() == 2);
    Expr l = EvalPred(u, assms, toeval->left(), out);
    assert(isOpX<AND>(l) && l->arity() == 2);

    Expr r = EvalPred(u, assms, toeval->right(), out);
    assert(isOpX<AND>(r) && r->arity() == 2);

    return mk<AND>(
      OpIneqs(toeval, l->left(), r->left()),
      OpIneqs(toeval, l->right(), r->right()));
  }
  assert(0 && "EvalPred unimplemented for this op type");
}

}

#endif
