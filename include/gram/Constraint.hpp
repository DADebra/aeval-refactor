#ifndef CONSTRAINT__HPP__
#define CONSTRAINT__HPP__

#include "gram/Constraint.h"

#include "gram/CFGUtils.h"

using namespace ufo;

ExprUMap Constraint::strcache;

void Constraint::findExpansions(const ParseTree& pt, ExpansionsMap& outmap)
{
  return pt.foreachExpansion([&] (const Expr& nt, const ParseTree& prod)
  {
    outmap[nt].push_back(prod);
  });
}

ParseTree Constraint::findHighestParent(Expr data, const ParseTree& child)
{
  if (!child)
    return NULL;
  if (child.data() == data)
  {
    ParseTree nextparent = std::move(
      findHighestParent(data, child.parent()));
    if (nextparent)
      return nextparent; // We found a higher parent
    return child;
  }
  if (!child.parent())
    return NULL; // Couldn't find parent with given data
  return std::move(findHighestParent(data, child.parent()));
}

Expr Constraint::stoe(Expr e)
{
  assert(isOpX<STRING>(e));
  assert(strcache.count(e) != 0);
  return strcache.at(e);
}

void Constraint::foreachExpans(Expr con, const ExpansionsMap& expmap,
  function<bool(const PtExpMap&)> func)
{
  ExprVector fapps(expmap.size());
  filter(con, [] (Expr e) {
    return isOpX<FAPP>(e) && e->arity() == 1; }, fapps.begin());
  // Note that because of the internal ExprSet that dagVisit uses,
  //   we don't need to purge duplicates from `fapps`.
  ExprVector from;
  for (auto &f : fapps)
    if (f && expmap.count(f) != 0) from.push_back(f);
  vector<ParseTree> to(from.size());
  auto makemap = [&] () -> PtExpMap
  {
    PtExpMap ret;
    for (int i = 0; i < from.size(); ++i)
    {
      bool insertgood = ret.emplace(from[i], to[i]).second;
      assert(insertgood);
    }
    return std::move(ret);
  };

  if (from.size() == 0)
  {
    // If there are no expansions, we still need to evaluate the constraint
    func(makemap());
    return;
  }

  function<bool(int)> perm = [&] (int pos)
  {
    if (pos == from.size())
    {
      if (!func(makemap()))
        return false;
    }
    else
      for (auto &expand : expmap.at(from[pos]))
      {
        to[pos] = expand;
        if (!perm(pos + 1))
          return false;
      }
    return true;
  };
  perm(0);
}

optional<cpp_int> Constraint::evaluateArithExpr(Expr arith, const PtExpMap& expmap,
  seen_type& se)
{
  auto aritharg = [&] (int i) -> Expr
  {
    if (expmap.count(arith->arg(i)) != 0)
      return expmap.at(arith->arg(i)).data();
    else
      return arith->arg(i);
  };
  if (isOpX<FAPP>(arith))
  {
    if (expmap.count(arith) != 0)
      return evaluateArithExpr(expmap.at(arith).data(), expmap, se);
    else
      return none;
  }

  if (isOpX<ITE>(arith))
  {
    tribool res = evaluateCmpExpr(aritharg(0), expmap, se);
    if (indeterminate(res))
      return none;
    if (res)
      return evaluateArithExpr(aritharg(1), expmap, se);
    else
      return evaluateArithExpr(aritharg(2), expmap, se);
  }

  if (isOpX<MPZ>(arith))   return lexical_cast<cpp_int>(arith);
  if (arith->arity() != 2) return none;

  optional<cpp_int> lhs = evaluateArithExpr(aritharg(0), expmap, se);
  if (!lhs) return none;
  cpp_int ilhs = *lhs;

  if (isOpX<UN_MINUS>(arith)) return optional<cpp_int>(-ilhs);
  if (isOpX<ABS>(arith))   return ilhs > 0 ? ilhs : -ilhs;

  optional<cpp_int> rhs = evaluateArithExpr(aritharg(1), expmap, se);
  if (!rhs) return none;
  cpp_int irhs = *rhs;

  if (isOpX<PLUS>(arith))  return optional<cpp_int>(ilhs + irhs);
  if (isOpX<MINUS>(arith)) return optional<cpp_int>(ilhs - irhs);
  if (isOpX<MULT>(arith))  return optional<cpp_int>(ilhs * irhs);
  if (isOpX<DIV>(arith) || isOpX<IDIV>(arith))
    return optional<cpp_int>(ilhs / irhs);
  if (isOpX<MOD>(arith))
  {
    // Copied from include/ae/ExprSimpl.hpp
    if (irhs < 0)
      irhs = -irhs;
    if (ilhs < 0)
      ilhs += ((-ilhs / irhs) + 1) * irhs;
    ilhs = ilhs % irhs;
    return ilhs;
  }
  return none;
}

tribool Constraint::evaluateCmpExpr(Expr cmp, const PtExpMap& expmap,
  seen_type& seenexpans)
{
  auto cmparg = [&] (int i) -> Expr
  {
    if (expmap.count(cmp->arg(i)) != 0)
      return expmap.at(cmp->arg(i)).data();
    else
      return cmp->arg(i);
  };

  string conn;
  if (isOpX<FAPP>(cmp))
    conn = lexical_cast<string>(bind::fname(cmp)->left());

  // simplifyArithm is also simplifying comparisons
  if (isOpX<FALSE>(cmp))
    return false;
  if (isOpX<TRUE>(cmp))
    return true;
  if (isOpX<NEG>(cmp))
    return !evaluateCmpExpr(cmp->left(), expmap, seenexpans);
  if (isOpX<EQ>(cmp) || (conn == "equal" && cmp->arity() > 2))
  {
    int si = conn == "equal" ? 1 : 0;
    optional<cpp_int> first = evaluateArithExpr(cmparg(si),
      expmap, seenexpans);
    if (!first && !isOpX<FAPP>(cmparg(si)) && !isOpX<MPZ>(cmparg(si)) &&
    !isOpX<MPQ>(cmparg(si)))
      return indeterminate;
    for (int i = si + 1; i < cmp->arity(); ++i)
    {
      if (first)
      {
        optional<cpp_int> inti = evaluateArithExpr(cmparg(i),
          expmap, seenexpans);
        if (!inti)
          return indeterminate;
        if (inti != first)
          return false;
      }
      else
      {
        if (!isOpX<FAPP>(cmparg(i)) && !isOpX<MPZ>(cmparg(i)) &&
        !isOpX<MPQ>(cmparg(i)))
          return indeterminate;
        if (cmparg(i) != cmparg(si))
          return false;
      }
    }
    return true;
  }
  if (isOpX<NEQ>(cmp) && cmp->arity() > 1)
  {
    for (int p1 = 0; p1 < cmp->arity(); ++p1)
    {
      optional<cpp_int> first = evaluateArithExpr(cmparg(p1),
        expmap, seenexpans);
      for (int p2 = p1 + 1; p2 < cmp->arity(); ++p2)
      {
        if (first)
        {
          optional<cpp_int> second = evaluateArithExpr(cmparg(0),
            expmap, seenexpans);
          if (!second)
            return indeterminate;
          if (*first == *second)
            return false;
        }
        if (!isOpX<FAPP>(cmparg(p1)) && !isOpX<MPZ>(cmparg(p1)) &&
        !isOpX<MPQ>(cmparg(p1)))
          return indeterminate;
        if (cmparg(p1) == cmparg(p2))
          return false;
      }
    }
    return true;
  }
  if (isOpX<AND>(cmp) || isOpX<OR>(cmp) || isOpX<XOR>(cmp))
  {
    bool doAnd = isOpX<AND>(cmp),
         doXor = isOpX<XOR>(cmp);
    tribool ret = evaluateCmpExpr(cmparg(0), expmap, seenexpans);
    for (int i = 1; i < cmp->arity(); ++i)
    {
      tribool subret = evaluateCmpExpr(cmparg(i), expmap, seenexpans);
      if (doXor)
        ret = (subret || ret) && !(subret && ret);
      else if (doAnd)
        ret = subret && ret;
      else
        ret = subret || ret;
    }
    return ret;
  }
  if (isOpX<IMPL>(cmp))
    return !evaluateCmpExpr(cmparg(0),expmap,seenexpans) ||
      evaluateCmpExpr(cmparg(1),expmap,seenexpans);
  if (isOpX<ITE>(cmp))
    return evaluateCmpExpr(cmparg(0),expmap,seenexpans) ?
      evaluateCmpExpr(cmparg(1),expmap,seenexpans) :
      evaluateCmpExpr(cmparg(2),expmap,seenexpans);
  if (isOpX<FAPP>(cmp) || isOpX<NEQ>(cmp))
  {
    if (conn == "equal" || isOpX<NEQ>(cmp))
    {
      Expr lhs;
      if (isOpX<NEQ>(cmp))
      {
        assert(cmp->arity() == 1);
        lhs = cmp->arg(0);
      }
      else
      {
        assert(cmp->arity() == 2);
        lhs = cmp->arg(1);
      }
      pair<Expr,ParseTree> key = make_pair(lhs, ParseTree(NULL));
      if (expmap.count(lhs) == 0)
        return true;

      bool firstinsert = seenexpans.count(key) == 0;
      bool res = seenexpans[key].insert(expmap.at(lhs).data()).second;
      return conn == "equal" ? firstinsert || !res : res;
    }
    else if (conn == "equal_under" || conn == "distinct_under")
    {
      if (cmp->arity() == 3)
      {
        assert(isOpX<FAPP>(cmp));
        Expr lhs = stoe(cmp->arg(1));
        Expr rhs = cmp->arg(2);

        // Self-equal/distinct
        if (expmap.count(rhs) == 0)
          return true;

        ParseTree rhsexp = expmap.at(rhs); // The Expr that RHS expands to

        ParseTree parent = findHighestParent(lhs, rhsexp);
        if (!parent)
          return true;
        pair<Expr,ParseTree> key = make_pair(rhs, parent);
        bool firstinsert = seenexpans.count(key) == 0;
        bool res = seenexpans[key].insert(rhsexp.data()).second;
        return conn == "equal_under" ? firstinsert || !res : res;
      }

      // Else, pairwise equal/distinct
      assert(cmp->arity() > 3);

      Expr lhs = stoe(cmp->arg(1));

      for (int p1 = 2; p1 < cmp->arity(); ++p1)
      {
        if (expmap.count(cmp->arg(p1)) == 0)
          continue;
        for (int p2 = p1 + 1; p2 < cmp->arity(); ++p2)
        {
          if (expmap.count(cmp->arg(p2)) == 0)
            continue;
          ParseTree exp1 = expmap.at(cmp->arg(p1));
          ParseTree par1 = findHighestParent(lhs, exp1);
          if (!par1)
            continue;
          ParseTree exp2 = expmap.at(cmp->arg(p2));
          ParseTree par2 = findHighestParent(lhs, exp2);
          if (!par2 || par1 != par2)
            continue;
          bool res;
          if (conn == "equal_under")
            res = exp1.data() == exp2.data();
          else
            res = exp1.data() != exp2.data();
          if (!res)
            return false;
        }
      }
      return true;
    }
    else if (conn == "expands")
    {
      Expr lhs = cmp->arg(1);
      Expr rhs = stoe(cmp->arg(2));
      if (expmap.count(lhs) == 0)
        return true;
      return expmap.at(lhs).data() == rhs;
    }
    else if (conn == "under")
    {
      Expr lhs = stoe(cmp->arg(1));
      Expr rhs = cmp->arg(2);
      if (expmap.count(rhs) == 0)
        return true;
      ParseTree parent = findHighestParent(lhs, expmap.at(rhs));

      return bool(parent);
    }
    else
      return indeterminate;
  }

  if (!isOp<ComparissonOp>(cmp))
    return indeterminate;
  if (cmp->arity() > 2)
    return indeterminate;

  optional<cpp_int> lo= evaluateArithExpr(cmp->arg(0),expmap,seenexpans),
                    ro= evaluateArithExpr(cmp->arg(1),expmap,seenexpans);
  if (!lo || !ro)
    return indeterminate;
  cpp_int li = *lo, ri = *ro;

  if (isOpX<LEQ>(cmp))
    return li <= ri;
  if (isOpX<GEQ>(cmp))
    return li >= ri;
  if (isOpX<LT>(cmp))
    return li < ri;
  if (isOpX<GT>(cmp))
    return li > ri;

  return indeterminate;
}

bool Constraint::doesSatExpr(Expr con, const ExpansionsMap& expmap) const
{
  bool needsolver = false;
  ExprVector assertexps;
  if (any)
    assertexps.push_back(mk<FALSE>(con->efac()));
  else
    assertexps.push_back(mk<TRUE>(con->efac()));

  //evalCmpExpr needs some shared state
  seen_type seenexpans;
  tribool ret = indeterminate;
  foreachExpans(con, expmap, [&] (const PtExpMap& exp)
  {
    tribool res = evaluateCmpExpr(con, exp, seenexpans);
    if (indeterminate(res))
    {
      // We (maybe) don't want Z3 to evaluate variables as
      //   non-determinate integers.
      RW<function<Expr(Expr)>> rw(new function<Expr(Expr)>(
        [&exp] (Expr e) -> Expr
      {
        if (isOpX<FAPP>(e) && exp.count(e) != 0)
          e = exp.at(e).data();
        if ((isOpX<EQ>(e) || isOpX<NEQ>(e)) &&
        all_of(e->args_begin(), e->args_end(), isOpX<FAPP,Expr>))
        {
          ExprVector args(e->arity());
          for (int i = 0; i < e->arity(); ++i)
            // Using memory location here as an easy way to get
            //   different symbolic variables to be
            //   a). predictable and b). unique
            args[i] = mkMPZ((unsigned long)e->arg(i), e->efac());
          return e->efac().mkNary(e->op(), args);
        }
        return e;
      }));
      Expr z3exp = dagVisit(rw, con);
      //m_smt_solver.assertExpr(exp);
      assertexps.push_back(z3exp);
      needsolver = true;
    }
    else if (!res && !any)
    {
      ret = false;
      return false;
    }
    else if (res && any)
    {
      ret = true;
      return false;
    }
    return true;
  });
  if (!indeterminate(ret))
    return bool(ret);

  assert(!needsolver);
  /*if (needsolver)
  {
    m_smt_solver.reset();

    if (any)
      m_smt_solver.assertExpr(m_efac.mkNary(OR(), assertexps));
    else
      m_smt_solver.assertExpr(m_efac.mkNary(AND(), assertexps));

    static unordered_map<Expr,bool> didcomplain;
    if (!didcomplain[origcon])
    {
      outs() << "NOTE: Invoking SMT solver to evaluate constraint: " <<
        origcon->right() << "\n Freqhorn will go much slower!\n";
      didcomplain[origcon] = true;
    }
    tribool res = m_smt_solver.solve();
    if (indeterminate(res))
    {
      outs() << "ERROR: Indeterminate result in evaluating constraints:\n";
      m_smt_solver.toSmtLib(outs());
      outs() << endl;
      assert(0);
    }
    if (!res && !any)
      return false;
    else if (res && any)
      return true;
  }*/

  if (any)
    return false;
  else
    return true;
}

int Constraint::calculateRecDepth(const ExpansionsMap& expmap, Expr nt)
{
  if (expmap.count(nt) == 0)
    return 0;
  int depth = 0;
  for (const auto &pt : expmap.at(nt))
    if (CFGUtils::isRecursive(pt.data(), nt))
      ++depth;
  return depth;
}

bool Constraint::doesSat(const ParseTree& pt) const
{
  ExpansionsMap expmap;
  findExpansions(pt, expmap);

  Expr con = expr;
  RW<function<Expr(Expr)>> fapprw(new function<Expr(Expr)>(
    [&expmap, &pt, this] (Expr e) -> Expr
  {
    auto btoe = [&] (bool b) -> Expr
    {
      return b ? mk<TRUE>(e->efac()) : mk<FALSE>(e->efac());
    };

    if (isOpX<FAPP>(e))
    {
      string conname = lexical_cast<string>(bind::fname(e)->left());
      if (conname == "present")
      {
        Expr lhs = stoe(e->arg(1));
        // Could be evaluated in evaluateCmpExpr, but I want to keep
        //   the framework of global expression evaluation here.
        function<bool(const ParseTree&)> existhelper =
          [&] (const ParseTree& root) -> bool
        {
          if (root.data() == lhs)
            return true;
          for (auto& child : root.children())
            if (existhelper(child))
              return true;
          return false;
        };
        return btoe(existhelper(pt));
      }
      else if (conname == "maxrecdepth")
      {
        Expr lhs = stoe(e->arg(1));
        if (expmap.count(lhs) == 0)
          return mkMPZ(cpp_int(0), e->efac());
        int deepest = 0;
        for (const auto &pt : expmap.at(lhs))
        {
          int depth = calculateRecDepth(expmap, lhs);
          if (depth > deepest)
            deepest = std::move(depth);
        }
        return mkMPZ(cpp_int(deepest), e->efac());
      }
      else
        return e;
    }
    /*else if (isOpX<NEG>(e) && isOpX<NEQ>(e->left()) &&
      e->left()->arity() == 1)
    {
      // Shared between all objects; OK
      static unordered_map<Expr,Expr> eqapp;
      // Doesn't matter if index by e or e->left()
      if (eqapp.count(e->left()) != 0)
        return eqapp.at(e->left());
      Expr eqdecl = bind::fdecl(
        mkTerm(string("equal"), m_efac),
        ExprVector{ bind::typeOf(e->left()->left()) });
      eqapp.emplace(e->left(),
        bind::fapp(eqdecl, e->left()->left(), Expr()));
      return eqapp.at(e->left());
    }
    else if (isOpX<NEG>(e) && isOpX<FAPP>(e->left()))
    {
      Expr nfdecl = e->left()->left();
      string nfname = lexical_cast<string>(nfdecl->left());
      if (nfname == "under" || nfname == "not_under")
      {
        string opposite = nfname == "not_under" ? "under" : "not_under";
        // Shared between all objects; OK
        static unordered_map<Expr,Expr> notuapp;
        // Doesn't matter if index by e or e->left()
        if (notuapp.count(e->left()) != 0)
          return notuapp.at(e->left());
        Expr notudecl = bind::fdecl(
          mkTerm(string(opposite), m_efac),
          ExprVector{ nfdecl->arg(1), nfdecl->arg(2) });
        assert(e->left()->arity() == 3);
        notuapp.emplace(e->left(), bind::reapp(e->left(), notudecl));
        return notuapp.at(e->left());
      }
      else if (nfname == "equal")
      {
        return mk<NEQ>(e->left()->right());
      }
      else
        return e;
    }*/
    else
      return e;
  }));
  con = dagVisit(fapprw, con);
  if (!doesSatExpr(con, expmap))
    return false;

  return true;
}
#endif
