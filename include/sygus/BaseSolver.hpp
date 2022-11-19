#ifndef __BASESOLVER_HPP__
#define __BASESOLVER_HPP__

#include <boost/logic/tribool.hpp>
#include "ufo/Expr.hpp"
#include "ufo/ExprLlvm.hpp"
#include "expr/ExprEval.hpp"
#include "utils/SetHash.hpp"
#include <fstream>

namespace ufo
{
using namespace std;
using namespace boost;

class BaseSolver
{
  protected:
  typedef unordered_map<const SynthFunc*, Expr> DefMap; // K: func, V: Def

  const SynthProblem &prob;
  Expr allcons; // Conjunction of all problem constraints
  Expr negallcons; // mkNeg(allcons)
  ExprFactory &efac;
  EZ3 &z3;
  SMTUtils u;
  SyGuSParams params;

  ExprVector faArgs; // Arguments to the FORALL used for '(Constant *)'
  bool hasanyconst = false; // True if some synth function uses '(Constant *)'

  string _errmsg; // Non-empty if Solve() returned false
  DefMap _foundfuncs;
  vector<const SynthFunc*> _foundfuncsorder; // see findFoundOrdering()

  public:
  const string& errmsg = _errmsg;
  const unordered_map<const SynthFunc*,Expr>& foundfuncs = _foundfuncs;
  const vector<const SynthFunc*>& foundfuncsorder = _foundfuncsorder;

  protected:

  // Find ordering of foundfuncs, such that
  // j > i implies that ret[i] doesn't depend on ret[j]
  void findFoundOrdering()
  {
    if (foundfuncsorder.size() == prob.synthfuncs.size())
      return;
    assert(foundfuncs.size() == prob.synthfuncs.size());

    _foundfuncsorder.reserve(foundfuncs.size());
    unordered_set<Expr> found; // K: SynthFunc.decl
    while (foundfuncsorder.size() != foundfuncs.size())
    {
      for (const auto &kv : foundfuncs)
      {
        if (found.count(kv.first->decl) != 0)
          continue;
        vector<Expr> fapps;
        filter(kv.second, [] (Expr e) { return isOpX<FAPP>(e); },
          inserter(fapps, fapps.begin()));
        bool dobreak = false;
        for (const Expr &f : fapps)
          if (prob.declToFunc.count(f->left()) != 0 && found.count(f->left()) == 0)
          {
            dobreak = true;
            break; // We haven't included this fapp's dependencies yet
          }
        if (dobreak) continue;
        _foundfuncsorder.push_back(kv.first);
        found.insert(kv.first->decl);
      }
    }
  }

  // Can't use replaceAll because it'll infinitely loop for e.g. x->y, y->x
  Expr replaceAllCust(Expr ex, const ExprUMap& repMap)
  {
    ExprUMap visited;
    function<Expr(Expr)> visit = [&] (Expr e)
    {
      auto visiteditr = visited.find(e);
      if (visiteditr != visited.end())
        return visiteditr->second;

      Expr ret;
      auto repitr = repMap.find(e);
      if (repitr != repMap.end())
      {
        e = repitr->second;
      }
      if (!isOpX<FDECL>(e))
      {
        ExprVector newargs(e->arity());
        bool needupdate = false;
        for (int i = 0; i < e->arity(); ++i)
        {
          Expr newarg = visit(e->arg(i));
          if (!needupdate && newarg != e->arg(i))
            needupdate = true;
          newargs[i] = newarg;
        }
        if (needupdate)
          ret = e->efac().mkNary(e->op(), newargs);
        else
          ret = e;
      }
      else
        ret = e;
      visited[e] = ret;
      return ret;
    };
    return visit(ex);
  }

  // "Applies" `def` using arguments in `ffapp`
  Expr applyDefinition(Expr ffapp, const SynthFunc& func, Expr def)
  {
    ExprUMap replaceMap;
    assert(isOpX<FAPP>(ffapp));

    for (int i = 0; i < func.vars.size(); ++i)
    {
      Expr k = bind::fapp(func.vars[i]);
      Expr v = ffapp->arg(i + 1);
      if (k != v)
        replaceMap[k] = v;
    }
    if (replaceMap.size() == 0)
      return def;
    else
      return replaceAllCust(def, replaceMap);
  }

  // Replace applications of synth-fun's with their definitions
  Expr replaceFapps(Expr e, const DefMap& defs)
  {
    RW<function<Expr(Expr)>> recrw(new function<Expr(Expr)>(
      [&] (Expr e) -> Expr
      {
        if (isOpX<FAPP>(e))
        {
          auto funcitr = prob.declToFunc.find(e->left());
          if (funcitr != prob.declToFunc.end())
          {
            e = applyDefinition(e, *funcitr->second, defs.at(funcitr->second));
            e = replaceFapps(e, defs);
          }
        }
        return e;
      }));
    return dagVisit(recrw, e);
  }

  // Replaces '(ANY_CONST -1)' with a unique MPZ for each application in 'defs'
  void replaceAnyConsts(DefMap& defs, ExprUSet& anyConsts)
  {
    mpz_class constNum = -1;
    RW<function<Expr(Expr)>> constrw(new function<Expr(Expr)>(
      [&] (Expr e) -> Expr
      {
        if (!isOpX<FAPP>(e))
          return e;

        const string& fname = getTerm<string>(e->left()->left());
        if (fname == "ANY_CONST" && getTerm<mpz_class>(e->last()) == -1)
        {
          Expr constapp = fapp(e->left(), {mkTerm(++constNum, e->efac())});
          anyConsts.insert(constapp);
          return constapp;
        }

        return e;
      }
    ));
    for (auto& kv : defs)
      if (kv.first->hasanyconst)
        kv.second = visit(constrw, kv.second);
  }

  // True = Candidate definitions are always true
  tribool checkCands(DefMap& cands)
  {
    ExprUSet anyConsts;
    if (hasanyconst)
      replaceAnyConsts(cands, anyConsts);
    Expr tocheck = replaceFapps(allcons, cands);
    if (anyConsts.size() == 0)
      return !u.isSat(mk<NEG>(tocheck));

    if (faArgs.size() != 1)
    {
      faArgs.back() = tocheck;
      tocheck = mknary<FORALL>(faArgs);
    }
    tribool ret = u.isSat(tocheck);
    if (!ret)
      return false;
    else if (indeterminate(ret))
      //assert(0 && "Handling unknowns from Z3 for (Constant *) is unimplemented");
      return indeterminate;

    ExprUMap constReplaceMap;
    for (const Expr& c : anyConsts)
    {
      Expr foundConst = u.getModel(c);
      if (!foundConst)
        //assert(0 && "Handling no model from Z3 for (Constant *) is unimplemented");
        return indeterminate;
      constReplaceMap[c] = foundConst;
    }
    for (auto& kv : cands)
      kv.second = replaceAll(kv.second, constReplaceMap);
    return true;
  }

  // Check the found functions against the constraints
  bool sanityCheck()
  {
    bool doExtraCheck = false;
    Expr checkcons = conjoin(prob.constraints, efac);
    ExprUSet unused;
    checkcons = replaceFapps(checkcons, foundfuncs);

    ZSolver<EZ3> smt(z3);
    smt.assertExpr(mk<NEG>(checkcons));
    tribool ret = smt.solve();
    if (ret && params.debug)
    {
      outs() << "Sanity check:\n";
      smt.toSmtLib(outs());
      ExprSet allVars;
      filter(allcons, bind::IsConst(), inserter(allVars, allVars.begin()));
      ZSolver<EZ3>::Model* m = smt.getModelPtr();
      if (m)
      {
        outs() << "Model for sanity check:\n";
        for (const Expr& v : allVars)
          outs() << v << " = " << m->eval(v) << endl;
      }
    }

    if (doExtraCheck || ret)
    {
      int noz3 = system("z3 -version >&-");
      if (noz3)
      {
        if (doExtraCheck)
          errs() << "Warning: Extra check requested but Z3 not installed. Skipping.\n";
        return bool(!ret);
      }

      char tmpfilename[7];
      strcpy(tmpfilename, "XXXXXX");
      int tmpfilefd = mkstemp(tmpfilename);
      assert(tmpfilefd);
      ostringstream os;
      ofstream tmpfilestream(tmpfilename);

      for (const SynthFunc* func : foundfuncsorder)
        os << func->GetDefFun(foundfuncs.at(func), u, false) << "\n";

      vector<Expr> fapps;
      Expr negconsts = mk<NEG>(conjoin(prob.constraints, efac));
      filter(negconsts, [](Expr e){return isOpX<FAPP>(e);},
        inserter(fapps, fapps.begin()));

      for (const Expr &f : fapps)
        if (prob.declToFunc.count(f->left()) == 0)
          os << z3.toSmtLibDecls(f) << "\n";

      os << "(assert "; u.print(negconsts, os); os << ")\n(check-sat)\n";

      os.flush();
      tmpfilestream << os.str();
      tmpfilestream.flush();

      int zret = system((string("z3 ") + tmpfilename + " >&-").c_str());
      if (zret && (!ret || indeterminate(ret)))
      {
        outs() << os.str();
        system((string("z3 -model ") + tmpfilename).c_str());
        ret = true;
      }
      remove(tmpfilename);
    }

    return bool(!ret);
  }

  public:
  BaseSolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) :
    prob(_prob), efac(_efac), z3(_z3), u(efac), params(p)
  {
    allcons = conjoin(prob.constraints, efac);
    negallcons = mkNeg(allcons);
    faArgs = prob.vars;
    faArgs.push_back(NULL); // To be filled in 'checkCands'
    for (const auto& func : prob.synthfuncs)
      hasanyconst |= func.hasanyconst;
  }

  // Returns success: true == solved, false == infeasible, indeterminate == fail
  virtual tribool Solve() = 0;
};

}

#endif
