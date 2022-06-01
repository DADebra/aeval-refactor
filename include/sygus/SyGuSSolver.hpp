#ifndef __SYGUSSOLVER_HPP__
#define __SYGUSSOLVER_HPP__

#include "ae/AeValSolver.hpp"
#include <boost/logic/tribool.hpp>
#include "ufo/ExprLlvm.hpp"
#include <fstream>

namespace ufo
{
using namespace std;
using namespace boost;

const int TOTALMAXRECDEPTH = 5; // The absolute deepest to go before terminating

class SyGuSSolver
{
  typedef unordered_map<const SynthFunc*, Expr> DefMap; // K: func, V: Def

  private:
  SynthProblem prob;
  Expr allcons; // Conjunction of all problem constraints
  ExprFactory &efac;
  EZ3 &z3;
  SMTUtils u;
  SyGuSParams params;

  unordered_map<Expr, const SynthFunc*> declToFunc; // K: FDECL, V: SynthFunc

  string _errmsg; // Non-empty if Solve() returned false
  DefMap _foundfuncs;
  vector<const SynthFunc*> _foundfuncsorder; // see findFoundOrdering()

  public:
  const string& errmsg = _errmsg;
  const unordered_map<const SynthFunc*,Expr>& foundfuncs = _foundfuncs;
  const vector<const SynthFunc*>& foundfuncsorder = _foundfuncsorder;

  private:

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
          auto funcitr = declToFunc.find(e->left());
          if (funcitr != declToFunc.end())
          {
            e = applyDefinition(e, *funcitr->second, defs.at(funcitr->second));
          }
        }
        return e;
      }));
    return dagVisit(recrw, e);
  }

  tribool checkCands(const DefMap& cands)
  {
    Expr tocheck = replaceFapps(allcons, cands);
    return !u.isSat(mk<NEG>(tocheck));
  }

  // Check the found functions against the constraints
  bool sanityCheck()
  {
    const bool doExtraCheck = false;
    Expr checkcons = conjoin(prob.constraints, efac);
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

  tribool solveWithAeval()
  {
    if (prob.singleapps.size() != prob.synthfuncs.size())
    {
      _errmsg = "Single-invocation solver doesn't support multi-application functions (" + to_string(prob.synthfuncs.size() - prob.singleapps.size()) + " found)";
      return indeterminate;
    }

    ExprUMap replaceMap, replaceRevMap;

    unordered_map<Expr,const SynthFunc*> varToFunc; // K: funcvar (below)

    vector<Expr> faArgs, exArgs;
    ExprSet exVars;
    for (const SynthFunc& func : prob.synthfuncs)
    {
      Expr funcsort = func.decl->last();
      Expr funcvar = mkConst(mkTerm<string>(getTerm<string>(func.decl->first()) + "_out", efac), funcsort);
      Expr singlefapp = prob.singleapps.at(func.decl);
      replaceMap[singlefapp] = funcvar;
      replaceRevMap[funcvar] = singlefapp;
      exArgs.push_back(funcvar->first());
      exVars.insert(funcvar);
      varToFunc[funcvar] = &func;
    }
    allcons = replaceAll(allcons, replaceMap);

    for (const auto& kv : prob.singleapps)
      for (int i = 1; i < kv.second->arity(); ++i)
        faArgs.push_back(kv.second->arg(i)->left());
    exArgs.push_back(allcons);
    faArgs.push_back(mknary<EXISTS>(exArgs));
    Expr aeProb = mknary<FORALL>(faArgs);
    aeProb = regularizeQF(aeProb);
    aeProb = convertIntsToReals<DIV>(aeProb);
    if (params.debug > 1)
      { outs() << "Sending to aeval: "; u.print(aeProb); outs() << endl; }

    AeValSolver ae(mk<TRUE>(efac), aeProb->last()->last(), exVars, params.debug, true);

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
      // AE-VAL returns (= fname def)
      Expr funcs_conj = ae.getSkolemFunction(true);
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

  tribool solveWithEnum()
  {
    for (const auto& func : prob.synthfuncs)
      if (!func.hasgram)
      {
        _errmsg = "Enumerative solver currently doesn't work without a grammar given in the SyGuS problem";
        return indeterminate;
      }

    TravParams tparams;
    tparams.SetDefaults();
    // TODO: To be changed when NewTrav is quicker and more memory efficient.
    tparams.method = TPMethod::CORO;
    tparams.maxrecdepth = TOTALMAXRECDEPTH;
    tparams.iterdeepen = true;

    // Create a "super" grammar which will synthesize permutations of
    // candidates for all of the functions to synthesize.
    Grammar supergram;
    vector<const SynthFunc*> funcorder;
    if (prob.synthfuncs.size() == 1)
      supergram = prob.synthfuncs[0].gram;
    else
    {
      // G' -> f(G1, G2, G3)
      ExprVector newrootdecl, newrootapp;
      newrootdecl.push_back(mkTerm(string("supergramfunc"), efac));
      newrootapp.push_back(NULL); // Space for eventual FDECL

      unordered_map<const SynthFunc*, ExprUMap> ntmap;

      for (const auto &func : prob.synthfuncs)
      {
        funcorder.push_back(&func);

        ExprUMap& fntmap = ntmap[&func];
        string funcname = getTerm<string>(func.decl->left());

        for (const auto& kv : func.gram.prods)
        {
          NT newnt = supergram.addNt(funcname + "_" +
            getTerm<string>(kv.first->left()->left()), kv.first->left()->last());
          fntmap[kv.first] = newnt;

          for (const Expr& prod : kv.second)
            supergram.addProd(newnt, replaceAll(prod, fntmap), func.gram.priomap.at(kv.first).at(prod));
        }

        // Just so we know not to expand them; the created *_VARS won't be used
        for (const auto& kv : func.gram.vars)
          for (const Var& var : kv.second)
            supergram.addVar(var);
        for (const auto& kv : func.gram.consts)
          for (const Expr& c : kv.second)
            supergram.addConst(c);

        Expr newroot = fntmap[func.gram.root];
        newrootdecl.push_back(typeOf(newroot));
        newrootapp.push_back(newroot);
      }

      Expr roottype = mk<BOOL_TY>(efac); // Can be anything
      newrootdecl.push_back(roottype);
      Expr nredecl = mknary<FDECL>(newrootdecl);

      newrootapp[0] = nredecl;
      NT newroot = supergram.addNt("supergramroot", roottype);
      supergram.setRoot(newroot);

      supergram.addProd(newroot, mknary<FAPP>(newrootapp));
    }

    GramEnum ge(supergram, &tparams, false, params.debug);
    DefMap cands;
    auto parseExpr = [&] (Expr cand)
    {
      if (prob.synthfuncs.size() > 1)
        for (int i = 1; i < cand->arity(); ++i)
          cands[funcorder[i - 1]] = cand->arg(i);
      else
        cands[&prob.synthfuncs[0]] = cand;
    };
    while (!ge.IsDone())
    {
      Expr newcand = ge.Increment();
      if (!newcand)
        break;
      parseExpr(newcand);
      if (checkCands(cands))
      {
        _foundfuncs = cands;
        if (params.debug) outs() << "Candidate found at recursion depth " + to_string(ge.GetCurrDepth()) << endl;
        return true;
      }
    }

    if (supergram.isInfinite())
    {
      _errmsg = "Unable to find solution for max recursion depth " + to_string(tparams.maxrecdepth);
      return indeterminate;
    }
    else
    {
      _errmsg = "No solution in grammar";
      return false;
    }
  }

  public:
  SyGuSSolver(SynthProblem _prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) :
    prob(_prob), efac(_efac), z3(_z3), u(efac), params(p)
  {
    for (const auto &func : prob.synthfuncs)
      declToFunc.emplace(func.decl, &func);
    allcons = conjoin(prob.constraints, efac);
  }

  // Returns success: true == solved, false == infeasible, indeterminate == fail
  tribool Solve()
  {
    prob.Analyze();

    tribool ret;

    if (params.method == SPMethod::SINGLE)
      ret = solveWithAeval();
    else if (params.method == SPMethod::ENUM)
      ret = solveWithEnum();
    else
    {
      _errmsg = "No solving method selected";
      return indeterminate;
    }
    if (!ret || indeterminate(ret))
      return ret;

    if (foundfuncs.size() != prob.synthfuncs.size())
    {
      _errmsg = "[Program Error] Solver invoked on " +
        to_string(prob.synthfuncs.size()) + " functions but only synthesized " +
        to_string(foundfuncs.size()) + " of them";
      return indeterminate;
    }

    findFoundOrdering();

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
