#ifndef __EXPRNORM_HPP__
#define __EXPRNORM_HPP__

#include "ufo/Expr.hpp"

namespace ufo
{

Expr plusjoin(const ExprVector &args)
{
  if (args.size() == 1)
    return args[0];
  else
    return mknary<PLUS>(args);
}

Expr _normalizeLIA(const Expr &e, const ExprUSet& vars, bool normrec = true)
{
  static unordered_set<Expr> isNormed;
  if (isNormed.count(e) != 0)
    return e;
  Expr eone = mkTerm<mpz_class>(1, e->efac());
  Expr enegone = mkTerm<mpz_class>(-1, e->efac());
  if (isLit(e))
  {
    isNormed.insert(e);
    return e;
  }
  else if (isOpX<FAPP>(e))
  {
    isNormed.insert(e);
    return e;
  }
  else if (isOpX<MULT>(e))
  {
    Expr eleft = e->left(), eright = e->right();
    if (normrec) eleft = _normalizeLIA(eleft, vars, normrec);
    Expr econst, erest;
    if (isOpX<MPZ>(eleft))
    { econst = eleft; erest = eright; }
    else if (isOpX<MPZ>(eright))
    { econst = eright; erest = eleft; }
    else
      assert(0 && "Formula given to normalizeLIA not in LIA");

    mpz_class c = getTerm<mpz_class>(econst);
    if (c < 0)
    {
      c = -c;
      econst = mkTerm<mpz_class>(c, econst->efac());
      erest = mk<UN_MINUS>(erest);
      if (normrec) erest = _normalizeLIA(erest, vars, normrec);
    }
    else if (normrec)
      erest = _normalizeLIA(erest, vars, normrec);

    if (isOpX<FAPP>(erest) ||
        (isOpX<UN_MINUS>(erest) && isOpX<FAPP>(erest->left())))
    {
      Expr ret = mk<MULT>(econst, erest);
      isNormed.insert(ret);
      return std::move(ret);
    }
    if (isOpX<MPZ>(erest))
    {
      Expr ret = mk<MULT>(
        mkTerm<mpz_class>(c * getTerm<mpz_class>(erest), erest->efac()), eone);
      isNormed.insert(ret);
      return std::move(ret);
    }

    if (!isOpX<PLUS>(erest))
    {
      assert(isOpX<MULT>(erest));
      Expr ret = mk<MULT>(
        mkTerm<mpz_class>(c*getTerm<mpz_class>(erest->left()), erest->efac()),
        erest->right());
      isNormed.insert(ret);
      return std::move(ret);
    }

    ExprVector newrest;
    for (const Expr &arg : *erest)
    {
      assert(isOpX<MULT>(arg));
      newrest.push_back(mk<MULT>(
        mkTerm<mpz_class>(c * getTerm<mpz_class>(arg->left()), arg->efac()),
        arg->right()));
    }
    Expr ret = plusjoin(newrest);
    isNormed.insert(ret);
    return std::move(ret);
  }
  else if (isOpX<UN_MINUS>(e))
  {
    if (isOpX<MPZ>(e->left()))
    {
      Expr ret = mkTerm<mpz_class>(-getTerm<mpz_class>(e->left()), e->efac());
      isNormed.insert(ret);
      return std::move(ret);
    }
    else if (isOpX<FAPP>(e->left()))
    {
      Expr ret = mk<MULT>(enegone, e->left());
      isNormed.insert(ret);
      return std::move(ret);
    }
    Expr norme = e->left();
    if (normrec) norme = _normalizeLIA(norme, vars, normrec);
    if (isOpX<MULT>(norme))
    {
      const mpz_class &c = getTerm<mpz_class>(norme->left());
      if (norme->right() == eone)
      {
        Expr ret = mk<MULT>(mkTerm<mpz_class>(-c, norme->efac()), norme->right());
        isNormed.insert(ret);
        return std::move(ret);
      }
      else if (isOpX<UN_MINUS>(norme->right()))
      {
        Expr ret = mk<MULT>(norme->left(), norme->right()->left());
        isNormed.insert(ret);
        return std::move(ret);
      }
      else
      {
        assert(isOpX<FAPP>(norme->right()));
        Expr ret = mk<MULT>(norme->left(), mk<UN_MINUS>(norme->right()));
        isNormed.insert(ret);
        return std::move(ret);
      }
    }
    assert(isOpX<PLUS>(norme));
    if (!normrec)
    {
      isNormed.insert(norme);
      return std::move(norme);
    }
    ExprVector newe;
    for (const Expr &arg : *norme)
    {
      mpz_class c = getTerm<mpz_class>(arg->left());
      newe.push_back(mk<MULT>(mkTerm<mpz_class>(-c, arg->efac()), arg->right()));
    }
    Expr ret = plusjoin(newe);
    isNormed.insert(ret);
    return std::move(ret);
  }
  else if (isOpX<PLUS>(e) || isOpX<MINUS>(e))
  {
    mpz_class negmult = isOpX<PLUS>(e) ? 1 : -1;
    map<Expr,mpz_class> varToCoef;
    for (const Expr &var : vars) varToCoef[var] = 0;
    varToCoef[eone] = 0;
    for (int i = 0; i < e->arity(); ++i)
    {
      const Expr &arg = e->arg(i);
      mpz_class mult = i == 0 ? 1 : negmult;
      Expr newarg = arg;
      if (normrec) newarg = _normalizeLIA(arg, vars, normrec);
      if (isOpX<PLUS>(newarg))
        for (const Expr &argarg : *newarg)
        {
          if (isOpX<MPZ>(argarg))
            varToCoef[eone] += mult * getTerm<mpz_class>(argarg);
          else if (isOpX<FAPP>(argarg))
            varToCoef[argarg] += mult;
          else
            varToCoef[argarg->right()] +=
              mult * getTerm<mpz_class>(argarg->left());
        }
      else
      {
        if (isOpX<MPZ>(newarg))
          varToCoef[eone] += mult * getTerm<mpz_class>(newarg);
        else if (isOpX<FAPP>(newarg))
          varToCoef[newarg] += mult;
        else
          varToCoef[newarg->right()] +=
            mult * getTerm<mpz_class>(newarg->left());
      }
    }
    ExprVector newe;
    for (const auto &var_coef : varToCoef)
      newe.push_back(mk<MULT>(
        mkTerm(var_coef.second, e->efac()), var_coef.first));
    Expr ret = plusjoin(newe);
    isNormed.insert(ret);
    return std::move(ret);
  }
  else
    assert(0 && "Unsupported Op in normalizeLIA");
}
Expr normalizeLIA(const Expr &e, const ExprUSet& vars)
{
  Expr eone = mkTerm<mpz_class>(1, e->efac());
  Expr ret = _normalizeLIA(e, vars, true);
  if (!isOpX<PLUS>(ret))
  {
    if (!isOpX<MULT>(ret))
    {
      if (isOpX<MPZ>(ret))
        ret = mk<MULT>(ret, eone);
      else
        ret = mk<MULT>(eone, ret);
    }
    ret = _normalizeLIA(mk<PLUS>(ret), vars, false);
  }
  return ret;
}

template <typename T>
Expr boxHull(const T& funcs_begin, const T& funcs_end,
  const ExprUSet& vars, const Expr &nt)
{
  map<Expr,mpz_class> varToMaxCoef, varToMinCoef;
  for (auto itr = funcs_begin; itr != funcs_end; ++itr)
  {
    Expr func = *itr;
    Expr lbound = normalizeLIA(func->left()->right(), vars),
         ubound = normalizeLIA(func->right()->right(), vars);
    for (const Expr &arg : *lbound)
    {
      const mpz_class &c = getTerm<mpz_class>(arg->left());
      if (c < varToMinCoef[arg->right()])
        varToMinCoef[arg->right()] = c;
    }
    for (const Expr &arg : *ubound)
    {
      const mpz_class &c = getTerm<mpz_class>(arg->left());
      if (c > varToMaxCoef[arg->right()])
        varToMaxCoef[arg->right()] = c;
    }
  }
  ExprVector newl, newu;
  for (const auto &var_coef : varToMinCoef)
    newl.push_back(mk<MULT>(
      mkTerm(var_coef.second, var_coef.first->efac()), var_coef.first));
  for (const auto &var_coef : varToMaxCoef)
    newu.push_back(mk<MULT>(
      mkTerm(var_coef.second, var_coef.first->efac()), var_coef.first));
  return mk<AND>(
    mk<GEQ>(nt, plusjoin(newl)), mk<LEQ>(nt, plusjoin(newu)));
}

}

#endif
