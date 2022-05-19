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
    assert(prob.synthfuncs.size() == 1);

    Expr funcdecl = prob.synthfuncs[0].decl;

    Expr allcons = conjoin(prob.constraints, efac);
    Expr funcsort = funcdecl->last();
    Expr funcout = mkConst(mkTerm<string>(getTerm<string>(funcdecl->first()) + "_out", efac), funcsort);
    Expr singlefapp = prob.singleapps.at(funcdecl);
    allcons = replaceAll(allcons, singlefapp, funcout);
    vector<Expr> faArgs;
    for (const Expr &var : prob.synthfuncs[0].vars)
      faArgs.push_back(var);
    vector<Expr> exArgs({ funcout->first(), allcons });
    faArgs.push_back(mknary<EXISTS>(exArgs));
    Expr aeProb = mknary<FORALL>(faArgs);
    aeProb = regularizeQF(aeProb);
    aeProb = convertIntsToReals<DIV>(aeProb);
    if (debug > 1)
      { outs() << "Sending to aeval: " << z3.toSmtLib(aeProb) << endl; }

    ExprSet exVars({fapp(funcout->first())});
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
      Expr func = ae.getSkolemFunction(true)->right();
      func = simplifyBool(simplifyArithm(func));
      _foundfuncs[&prob.synthfuncs[0]] = func;
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

    if (prob.synthfuncs.size() != 1)
    {
      _errmsg = "Solver currently doesn't support synthesizing multiple functions";
      return indeterminate;
    }

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
