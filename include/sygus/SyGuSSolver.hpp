#ifndef __SYGUSSOLVER_HPP__
#define __SYGUSSOLVER_HPP__

#include "ae/AeValSolver.hpp"
#include <boost/logic/tribool.hpp>
#include <fstream>

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

  unordered_map<Expr, const SynthFunc*> declToFunc; // K: FDECL, V: SynthFunc

  string _errmsg; // Non-empty if Solve() returned false
  unordered_map<const SynthFunc*,Expr> _foundfuncs; // K: func, V: Def
  vector<const SynthFunc*> _foundfuncsorder; // see findOrdering()

  public:
  const string& errmsg = _errmsg;
  const unordered_map<const SynthFunc*,Expr>& foundfuncs = _foundfuncs;
  const vector<const SynthFunc*>& foundfuncsorder = _foundfuncsorder;

  private:

  // Find ordering of foundfuncs, such that
  // j > i implies that ret[i] doesn't depend on ret[j]
  void findOrdering()
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
          if (declToFunc.count(f->left()) != 0 && found.count(f->left()) == 0)
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

  // "Applies" `def` using arguments in `fapp`
  Expr applyDefinition(Expr fapp, const SynthFunc& func, Expr def)
  {
    // TODO: Assumes single application
    vector<Expr> argfrom, argto;
    assert(isOpX<FAPP>(fapp));

    for (int i = 0; i < func.vars.size(); ++i)
      argfrom.push_back(bind::fapp(func.vars[i]));
    for (int i = 1; i < fapp->arity(); ++i)
      argto.push_back(fapp->arg(i));
    Expr out = replaceAll(def, argfrom, argto);
    out = replaceFapps(out);
    return out;
  }

  // Replace applications of synth-fun's with their definitions
  Expr replaceFapps(Expr e)
  {
    RW<function<Expr(Expr)>> recrw(new function<Expr(Expr)>(
      [&] (Expr e) -> Expr
      {
        if (isOpX<FAPP>(e))
        {
          for (const auto &kv : foundfuncs)
            if (kv.first->decl == e->left())
              return applyDefinition(e, *kv.first, kv.second);
        }
        return e;
      }));
    return dagVisit(recrw, e);
  }

  // Check the found functions against the constraints
  bool sanityCheck()
  {
    const bool doExtraCheck = false;
    Expr allcons = conjoin(prob.constraints, efac);
    allcons = replaceFapps(allcons);

    ZSolver<EZ3> smt(z3);
    smt.assertExpr(mk<NEG>(allcons));
    tribool ret = smt.solve();
    if (ret && debug)
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

    if (doExtraCheck)
    {
      int noz3 = system("z3 -version >&-");
      if (noz3)
      {
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
        if (declToFunc.count(f->left()) == 0)
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
        faArgs.push_back(kv.second->arg(i)->left());
    exArgs.push_back(allcons);
    faArgs.push_back(mknary<EXISTS>(exArgs));
    Expr aeProb = mknary<FORALL>(faArgs);
    aeProb = regularizeQF(aeProb);
    aeProb = convertIntsToReals<DIV>(aeProb);
    if (debug > 1)
      { outs() << "Sending to aeval: "; u.print(aeProb); outs() << endl; }

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
    prob(_prob), efac(_efac), z3(_z3), debug(_debug), u(efac)
  {
    for (const auto &func : prob.synthfuncs)
      declToFunc.emplace(func.decl, &func);
  }

  // Returns success: true == solved, false == infeasible, indeterminate == fail
  tribool Solve()
  {
    prob.Analyze();

    if (prob.singleapps.size() != prob.synthfuncs.size())
    {
      _errmsg = "Solver current doesn't support multi-application functions (" + to_string(prob.synthfuncs.size() - prob.singleapps.size()) + " found)";
      return indeterminate;
    }

    tribool ret;

    ret = solveSingleApps();
    if (!ret || indeterminate(ret))
      return ret;

    if (foundfuncs.size() != prob.singleapps.size())
    {
      _errmsg = "[Program Error] AE-VAL invoked on " + to_string(prob.singleapps.size()) +
        " single-app functions but only synthesized " + to_string(foundfuncs.size()) +
        " of them";
      return indeterminate;
    }

    if (foundfuncs.size() != prob.synthfuncs.size())
    {
      _errmsg = "[Program Error] Solver invoked on " +
        to_string(prob.synthfuncs.size()) + " functions but only synthesized " +
        to_string(foundfuncs.size()) + " of them";
      return indeterminate;
    }

    findOrdering();

    if (!sanityCheck())
    {
      _errmsg = "[Program Error] Found solutions failed sanity check";
      return indeterminate;
    }

    return true;
  }
};

}

#endif
