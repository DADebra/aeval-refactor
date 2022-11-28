#ifndef __ENUMSOLVER_HPP__
#define __ENUMSOLVER_HPP__

namespace ufo
{
using namespace std;
using namespace boost;

class EnumSolver : public BaseSolver
{
  private:

  public:

  EnumSolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) : BaseSolver(_prob, _efac, _z3, p) {}

  virtual tribool Solve()
  {
    for (const auto& func : prob.synthfuncs)
      if (!func.hasgram)
      {
        _errmsg = "Enumerative solver currently doesn't work without a grammar given in the SyGuS problem";
        return indeterminate;
      }

    TravParams tparams;
    tparams.SetDefaults();
    tparams.method = TPMethod::NEWTRAV;
    tparams.type = TPType::STRIPED;
    tparams.prio = TPPrio::BFS;
    tparams.dir = TPDir::RTL;
    tparams.order = TPOrder::REV;
    tparams.maxrecdepth = -1;
    tparams.iterdeepen = true;
    tparams.simplify = true;
    tparams.prune = false;

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
          for (const Expr& var : kv.second)
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

    int oldmaxdepth = -1;
    auto prunePathFn = [&] (const Expr& prod,const TravContext& ctx,
      const Expr& hole, const Expr& nt, int currdepth) -> tribool
    {
      // TODO: Pruning only implemented for simple cases
      if (prob.synthfuncs.size() > 1 ||
          prob.singleapps.size() != prob.synthfuncs.size())
        return false;

      Expr fnapp = prob.singleapps.at(&prob.synthfuncs[0]);

      ExprVector conj;
      for (const auto& kv : ctx.holes)
      {
        if (kv.second.nt != supergram.root)
          return false; // TODO: Handle assumptions for non-root NTs
        if (kv.second.depth >= oldmaxdepth)
          return indeterminate; // Not sure, haven't gotten to that depth yet.
        conj.push_back(replaceAll(negallcons, fnapp, kv.first));
      }
      conj.push_back(replaceAll(allcons, fnapp, ctx.holeyCtx));
      if (!u.isSat(mknary<AND>(conj)))
        return true; // Can prune!
      // Future invocations of this won't return true, since we know all we'll
      //   ever know about the NTs in this context.
      // TODO: Change if we arrive at NT summaries iteratively.
      return false;
    };

    //GramEnum ge(supergram, &tparams, prunePathFn, params.debug);
    // TODO: Re-enable pruning?
    GramEnum ge(supergram, &tparams, DefaultPrunePathFn, params.debug);
    DefMap cands;
    mpz_class candnum = 0;
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
      oldmaxdepth = ge.GetCurrDepth();
      Expr newcand = ge.Increment();
      if (params.debug > 1)
        outs() << "Iteration " << candnum << ": " << newcand << "\n";
      ++candnum;
      if (!newcand)
        break;
      parseExpr(newcand);
      if (checkCands(cands))
      {
        if (params.nonvac)
        {
          bool docontinue = false;
          for (const auto& kv : cands)
            if (isOpX<BOOL_TY>(typeOf(kv.second)))
              if (u.isTrue(kv.second) || u.isFalse(kv.second))
              {
                docontinue = true;
                break;
              }
          if (docontinue) continue;
        }

        parseExpr(ge.GetUnsimplifiedCand());
        assert(bool(checkCands(cands)));
        _foundfuncs = cands;
        if (params.debug) errs() << "Candidate found at recursion depth " <<
          to_string(ge.GetCurrDepth()) << endl;
        if (params.debug) errs() << "after " << candnum <<
          " iterations" << endl;
        ge.Finish(true);
        return true;
      }
    }

    ge.Finish(false);

    if (supergram.isInfinite())
    {
      _errmsg = "Unable to find solution for max recursion depth " + to_string(tparams.maxrecdepth);
      return indeterminate;
    }
    else if (hasanyconst)
    {
      _errmsg = "Unable to find solution with generated constants";
      return indeterminate;
    }
    else
    {
      _errmsg = "No solution in grammar";
      return false;
    }
  }

};

}

#endif
