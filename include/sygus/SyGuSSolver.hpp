#ifndef __SYGUSSOLVER_HPP__
#define __SYGUSSOLVER_HPP__

#include "ae/AeValSolver.hpp"
#include <boost/logic/tribool.hpp>

namespace ufo
{
using namespace std;
using namespace boost;

class SyGuSSolver
{
  private:
  SynthProblem prob;
  ExprFactory &efac;
  EZ3 &z3;
  SMTUtils u;
  int debug;

  string _errmsg; // Non-empty if Solve() returned false
  unordered_map<const SynthFunc*,Expr> _foundfuncs; // K: func, V: Def

  public:
  const string& errmsg = _errmsg;
  const unordered_map<const SynthFunc*,Expr>& foundfuncs = _foundfuncs;

  private:
  tribool solveSingleApps()
  {
    Expr allcons = conjoin(prob.constraints, efac);
    vector<Expr> from, to;

    unordered_map<Expr,const SynthFunc*> varToFunc; // K: funcvar (below)

    vector<Expr> faArgs, exArgs;
    ExprSet exVars;
    for (const SynthFunc& func : prob.synthfuncs)
    {
      Expr funcsort = func.decl->last();
      Expr funcvar = mkConst(mkTerm<string>(getTerm<string>(func.decl->first()) + "_out", efac), funcsort);
      Expr singlefapp = prob.singleapps.at(func.decl);
      from.push_back(singlefapp);
      to.push_back(funcvar);
      exArgs.push_back(funcvar->first());
      exVars.insert(funcvar);
      varToFunc[funcvar] = &func;
    }
    allcons = replaceAll(allcons, from, to);

    for (const auto& kv : prob.singleapps)
      for (int i = 1; i < kv.second->arity(); ++i)
        faArgs.push_back(kv.second->arg(i));
    exArgs.push_back(allcons);
    faArgs.push_back(mknary<EXISTS>(exArgs));
    Expr aeProb = mknary<FORALL>(faArgs);
    aeProb = regularizeQF(aeProb);
    aeProb = convertIntsToReals<DIV>(aeProb);
    if (debug > 1)
      { outs() << "Sending to aeval: " << z3.toSmtLib(aeProb) << endl; }

    AeValSolver ae(mk<TRUE>(efac), aeProb->last()->last(), exVars, debug, true);

    tribool aeret = ae.solve();
    if (indeterminate(aeret))
    {
      _errmsg = "AE-VAL returned unknown";
      return indeterminate;
    }
    else if (aeret)
    {
      _errmsg = "AE-VAL determined conjecture was infeasible";
      errs() << "Model for conjecture:\n";
      ae.printModelNeg(errs());
      errs() << "\n";
      return false;
    }
    else
    {
      // AE-VAL returns (= fname def)
      Expr funcs_conj = ae.getSkolemFunction(true);
      if (isOpX<EQ>(funcs_conj))
        // Just for ease of use; WON'T MARSHAL
        funcs_conj = mk<AND>(funcs_conj);
      assert(isOpX<AND>(funcs_conj));
      for (int i = 0; i < funcs_conj->arity(); ++i)
      {
        Expr func = funcs_conj->arg(i)->right();
        func = replaceAll(func, to, from); // Convert variables back to FAPPs
        func = simplifyBool(simplifyArithm(func));
        _foundfuncs[varToFunc.at(funcs_conj->arg(i)->left())] = func;
      }
      return true;
    }
  }

  public:
  SyGuSSolver(SynthProblem _prob, ExprFactory &_efac, EZ3 &_z3, int _debug) :
    prob(_prob), efac(_efac), z3(_z3), debug(_debug), u(efac) {}

  // Returns success: true == solved, false == infeasible, indeterminate == fail
  tribool Solve()
  {
    prob.Analyze();

    if (prob.singleapps.size() != prob.synthfuncs.size())
    {
      _errmsg = "Solver current doesn't support multi-application functions";
      return indeterminate;
    }

    return solveSingleApps();
  }
};

}

#endif
