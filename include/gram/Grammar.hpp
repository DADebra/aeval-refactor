#ifndef GRAMMAR__HPP__
#define GRAMMAR__HPP__

#include <random>

#include "gram/ParseTree.hpp"

namespace ufo
{

void Grammar::notifyListeners(ModClass cl, ModType ty)
{
  assert(cl != ModClass::NONE);
  assert(ty != ModType::NONE);
  for (const auto &l : modListeners)
    (*l)(cl, ty);
}

template <typename Sort>
NT Grammar::addNt(string name, ExprFactory& efac)
{
  return std::move(addNt(name, mk<Sort>(efac)));
}
NT Grammar::addNt(string name, Expr sort)
{
  // NOTE: This only works because of how Exprs are constructed. If the
  // 'NT' type changes, this will need to also be changed!
  NT newnt = mkConst(mkTerm(name, sort->efac()), sort);
  _nts.insert(newnt);
  if (_prods.count(newnt) == 0) _prods.emplace(newnt, vector<Expr>());
  return newnt;
}

bool Grammar::addProd(NT nt, Expr prod, mpq_class prio)
{
  if (find(_prods[nt].begin(), _prods[nt].end(), prod) != _prods[nt].end())
    // Production already added
    return false;
  _prods[nt].push_back(prod);
  _priomap[nt][prod] = prio;
  notifyListeners(ModClass::PROD, ModType::ADD);
  return true;
}

bool Grammar::delProd(NT nt, Expr prod)
{
  for (auto itr = _prods.begin(); itr != _prods.end(); ++itr)
    for (auto itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2)
      if (*itr2 == prod)
      {
        delProd(itr, itr2);
        return true;
      }
  return false;
}
vector<Expr>::iterator Grammar::delProd(
  unordered_map<Expr,vector<Expr>>::iterator itr1,
  vector<Expr>::const_iterator itr2)
{
  auto newitr = itr1->second.erase(itr2);
  _priomap[itr1->first].erase(*itr2);
  notifyListeners(ModClass::PROD, ModType::DEL);
  return newitr;
}

void Grammar::changePrio(NT nt, Expr prod, mpq_class prio)
{
  _priomap[nt][prod] = prio;
  notifyListeners(ModClass::PRIO, ModType::MOD);
}

bool Grammar::addConstraint(Expr cons, bool any)
{
  for (const auto& con : _constraints)
    if (con.expr == cons)
      return false;
  _constraints.push_back(Constraint(cons, any));
  notifyListeners(ModClass::CONSTRAINT, ModType::ADD);
  return true;
}
bool Grammar::delConstraint(Expr cons)
{
  for (auto itr = _constraints.begin(); itr != _constraints.end(); ++itr)
    if (itr->expr == cons)
    {
      delConstraint(itr);
      return true;
    }
  return false;
}
vector<Constraint>::iterator Grammar::delConstraint(vector<Constraint>::const_iterator itr)
{
  auto newitr = _constraints.erase(itr);
  notifyListeners(ModClass::CONSTRAINT, ModType::DEL);
  return newitr;
}

bool Grammar::addConst(Expr c, mpq_class prio)
{
  bool ret = _consts[bind::typeOf(c)].insert(c).second;
  if (ret)
  {
    Expr constNt = CFGUtils::constsNtName(bind::typeOf(c));
    if (_prods.count(constNt) == 0)
      _prods[constNt].push_back(c);
    else
    {
      constless cl;
      auto itr = _prods[constNt].begin();
      for (; itr != _prods[constNt].end(); ++itr) if (!cl(*itr, c)) break;
      _prods[constNt].insert(itr, c);
    }
    _priomap[constNt][c] = prio;
  }
  if (ret) notifyListeners(ModClass::CONST, ModType::ADD);
  return ret;
}

bool Grammar::delConst(Expr c)
{
  auto itr1 = _consts.find(bind::typeOf(c));
  if (itr1 == _consts.end())
    return false;
  auto itr2 = itr1->second.find(c);
  if (itr2 == itr1->second.end())
    return false;
  delConst(itr1, itr2);
  return true;
}
ConstMap::mapped_type::iterator Grammar::delConst(
    ConstMap::iterator itr1, ConstMap::mapped_type::const_iterator itr2)
{
  auto newitr = itr1->second.erase(itr2);
  bool delret = delProd(CFGUtils::constsNtName(itr1->first), *itr2);
  assert(delret);
  notifyListeners(ModClass::CONST, ModType::DEL);
  return newitr;
}

bool Grammar::addVar(Var var, mpq_class prio)
{
  bool ret = _vars[bind::typeOf(var)].insert(var).second;
  if (ret)
  {
    Expr varsTypeNt = CFGUtils::varsNtName(bind::typeOf(var), var.type);
    Expr varsAllNt = CFGUtils::varsNtName(bind::typeOf(var), VarType::NONE);
    for (const auto &varsNt : { varsTypeNt, varsAllNt })
    {
      if (_prods.count(varsNt) == 0)
        _prods[varsNt].push_back(var);
      else
      {
        varless vl;
        auto itr = _prods[varsNt].begin();
        for (; itr != _prods[varsNt].end(); ++itr) if (!vl(*itr, var)) break;
        _prods[varsNt].insert(itr, var);
      }
      _priomap[varsNt][var] = prio;
    }
  }
  if (ret) notifyListeners(ModClass::VAR, ModType::ADD);
  return ret;
}

bool Grammar::delVar(Var var)
{
  auto itr1 = _vars.find(bind::typeOf(var));
  if (itr1 == _vars.end())
    return false;
  auto itr2 = itr1->second.find(var);
  if (itr2 == itr1->second.end())
    return false;
  delVar(itr1, itr2);
  return true;
}
VarMap::mapped_type::iterator Grammar::delVar(VarMap::iterator itr1,
  VarMap::mapped_type::const_iterator itr2)
{
  auto newitr = itr1->second.erase(itr2);
  bool delret = delProd(CFGUtils::varsNtName(itr1->first, itr2->type), *itr2);
  assert(delret);
  notifyListeners(ModClass::VAR, ModType::DEL);
  return newitr;
}

bool Grammar::addModListener(std::shared_ptr<ModListener> listener)
{
  return modListeners.insert(listener).second;
}

bool Grammar::delModListener(std::shared_ptr<ModListener> listener)
{
  return modListeners.erase(listener) != 0;
}

bool Grammar::satsConstraints(const ParseTree& pt) const
{
  for (const auto& con : constraints)
    if (!con.doesSat(pt))
      return false;
  return true;
}

}
#endif
