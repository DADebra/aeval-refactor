#ifndef __SISOLVER_HPP__
#define __SISOLVER_HPP__

#include "sygus/BaseSolver.hpp"
#include "ae/AeValSolver.hpp"

namespace ufo
{
using namespace std;
using namespace boost;

class SISolver : public BaseSolver
{
  private:
  // The maximum partitioning size at which to compact the produced formula
  //  (since the compaction algorithm currently scales with the partitioning size)
  // Determined empirically
  const int MAX_ITERS_FOR_COMPACT = 14;


  // Sometimes AE-VAL returns an ITE tree with func=val nodes instead of the
  //   other way around. Rewrite so its func=ITE instead.
  Expr flattenITEDef(Expr ite)
  {
    if (isOpX<EQ>(ite))
      return ite;
    assert(isOpX<ITE>(ite));
    Expr newt = flattenITEDef(ite->right()), newe = flattenITEDef(ite->last());
    assert(isOpX<EQ>(newt) && isOpX<EQ>(newe));
    assert(newt->left() == newe->left());
    vector<Expr> newargs({ ite->left(), newt->right(), newe->right() });
    return mk<EQ>(newt->left(), mknary<ITE>(newargs));
  }

  public:

  SISolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) : BaseSolver(_prob, _efac, _z3, p) {}

  virtual tribool Solve()
  {
    if (prob.singleapps.size() != prob.synthfuncs.size())
    {
      _errmsg = "Single-invocation solver doesn't support multi-application functions (" + to_string(prob.synthfuncs.size() - prob.singleapps.size()) + " found)";
      return indeterminate;
    }

    ExprUMap replaceMap, replaceRevMap;

    unordered_map<Expr,const SynthFunc*> varToFunc; // K: funcvar (below)

    ExprSet exVars;
    for (const SynthFunc& func : prob.synthfuncs)
    {
      Expr funcsort = func.decl->last();
      Expr funcvar = mkConst(mkTerm<string>(getTerm<string>(func.decl->first()) + "_out", efac), funcsort);
      Expr singlefapp = prob.singleapps.at(&func);
      replaceMap[singlefapp] = funcvar;
      replaceRevMap[funcvar] = singlefapp;
      exVars.insert(funcvar);
      varToFunc[funcvar] = &func;
    }
    allcons = replaceAll(allcons, replaceMap);
    allcons = convertIntsToReals<DIV>(allcons);
    if (params.debug > 1)
      { outs() << "Sending to aeval: "; u.print(allcons); outs() << endl; }

    AeValSolver ae(mk<TRUE>(efac), allcons, exVars, params.debug, true);

    tribool aeret = ae.solve();
    if (indeterminate(aeret))
    {
      _errmsg = "Single-invocation solver returned unknown";
      return indeterminate;
    }
    else if (aeret)
    {
      _errmsg = "Single-invocation solver determined conjecture was infeasible";
      errs() << "Model for conjecture:\n";
      ae.printModelNeg(errs());
      errs() << "\n";
      return false;
    }
    else
    {
      // TODO: Make option?
      // TODO: Disable when AE-VAL's compaction is better?
      bool compact = ae.getPartitioningSize() <= MAX_ITERS_FOR_COMPACT;
      Expr funcs_conj = ae.getSkolemFunction(compact);
      // AE-VAL returns (= fname def)
      if (isOpX<EQ>(funcs_conj))
        // Just for ease of use; WON'T MARSHAL
        funcs_conj = mk<AND>(funcs_conj);
      else if (isOpX<ITE>(funcs_conj))
        // Just for ease of use; WON'T MARSHAL
        funcs_conj = mk<AND>(flattenITEDef(funcs_conj));
      assert(isOpX<AND>(funcs_conj));
      for (int i = 0; i < funcs_conj->arity(); ++i)
      {
        Expr func = funcs_conj->arg(i)->right();
        func = replaceAll(func, replaceRevMap); // Convert variables back to FAPPs
        func = simplifyBool(simplifyArithm(func));
        _foundfuncs[varToFunc.at(funcs_conj->arg(i)->left())] = func;
      }
      return true;
    }
  }
};
}

#endif
