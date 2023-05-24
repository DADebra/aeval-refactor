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

static inline Expr OpIneqs(Expr op, Expr l, Expr r, const ExprUSet& vars)
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
    return mk<LEQ>(lvar, normalizeLIA(mk(op->op(), lbound, rbound), vars));
  else
    return mk<GEQ>(lvar, normalizeLIA(mk(op->op(), lbound, rbound), vars));
}

inline ExprVector EvalPred(SMTUtils& u, const ExprUMap &assms, Expr toeval, Expr out, const ExprUSet &vars)
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
  {
    Expr ret = replaceAll(assms.at(toeval), toeval, out);
    ret = mk<AND>(
      mk<GEQ>(out, normalizeLIA(ret->left()->right(), vars)),
      mk<LEQ>(out, normalizeLIA(ret->right()->right(), vars)));
    return ExprVector{ret};
  }
  if (isOpX<FAPP>(toeval) || isLit(toeval))
  {
    Expr ret = normalizeLIA(toeval, vars);
    return ExprVector{mk<AND>(mk<GEQ>(out, ret), mk<LEQ>(out, ret))};
  }
  if (isOpX<ITE>(toeval))
  {
    ExprVector l = EvalPred(u, assms, toeval->right(), out, vars);
    ExprVector r = EvalPred(u, assms, toeval->last(), out, vars);
    if (l == r)
      return std::move(l);
    /*ExprVector conjs;
    for (const auto &hole_assm : assms)
      conjs.push_back(hole_assm.second);
    conjs.push_back(mk<NEG>(toeval->left()));
    if (!u.isSat(conjs))
      return std::move(l);
    conjs.back() = toeval->left();
    if (!u.isSat(conjs))
      return std::move(r);
    ExprVector condholes;
    filter(toeval->left(), [&](Expr e){return assms.count(e) != 0;},
      inserter(condholes, condholes.begin()));
    ExprVector vvars;
    for (const Expr& hole : condholes)
    {
      filter(assms.at(hole), [&](Expr e){return isOpX<MULT>(e) &&
        getTerm<mpz_class>(e->left()) != 0 && isOpX<FAPP>(e->right()); },
        inserter(vvars, vvars.begin()));
      if (vvars.size() != 0)
        break;
    }
    if (vvars.size() == 0)
    {
      l.insert(l.end(), r.begin(), r.end());
      return std::move(l);
    }*/
    ExprVector ret;
    ExprVector tmp{NULL, NULL};
    for (int i = 0; i < l.size() * r.size(); ++i)
    {
      tmp[0] = l[i % l.size()];
      tmp[1] = r[i / l.size()];
      ret.push_back(boxHull(tmp.begin(), tmp.end(), vars, out));
    }
    return std::move(ret);
  }
  if (isOpX<PLUS>(toeval) || isOpX<MINUS>(toeval))
  {
    bool isminus = false;
    if (isOpX<MINUS>(toeval))
    {
      isminus = true;
      toeval = mknary<PLUS>(toeval->args_begin(), toeval->args_end());
    }
    assert(toeval->arity() == 2);
    ExprVector lv = EvalPred(u, assms, toeval->left(), out, vars);

    ExprVector rv = EvalPred(u, assms, toeval->right(), out, vars);

    ExprVector ret;
    for (int i = 0; i < lv.size() * rv.size(); ++i)
    {
      const Expr& l = lv[i % lv.size()];
      Expr r = rv[i / lv.size()];
      if (isminus)
        r = mk<AND>(
          mk<GEQ>(out, normalizeLIA(mk<UN_MINUS>(r->right()->right()), vars)),
          mk<LEQ>(out, normalizeLIA(mk<UN_MINUS>(r->left()->right()), vars)));
      assert(isOpX<AND>(l) && l->arity() == 2);
      assert(isOpX<AND>(r) && r->arity() == 2);
      ret.push_back(mk<AND>(
        OpIneqs(toeval, l->left(), r->left(), vars),
        OpIneqs(toeval, l->right(), r->right(), vars)));
    }
    return std::move(ret);
  }
  assert(0 && "EvalPred unimplemented for this op type");
}

}

#endif
