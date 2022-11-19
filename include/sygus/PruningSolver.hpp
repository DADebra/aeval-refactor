#ifndef __PRUNINGSOLVER_HPP__
#define __PRUNINGSOLVER_HPP__

#include "sygus/BaseSolver.hpp"
#include "sygus/ExprEval.hpp"
#include "utils/SetHash.hpp"

namespace ufo
{
using namespace std;
using namespace boost;

class PruningSolver : public BaseSolver
{
  private:
  ZSolver<EZ3> wsolver;

  // Replaces first occurance in a post-fix traversal of 'e'
  std::pair<Expr,bool> _replaceOne(Expr e, Expr from, Expr to)
  {
    ExprVector args;
    if (e == from)
      return make_pair(to, true);

    if (isOpX<FAPP>(e) || isLit(e))
      return make_pair(e, false);

    bool didrepl = false;
    for (int i = 0; i < e->arity(); ++i)
    {
      if (!didrepl)
      {
        auto ret = _replaceOne(e->arg(i), from, to);
        if (ret.second)
          didrepl = true;
        args.push_back(ret.first);
      }
      else
        args.push_back(e->arg(i));
    }
    return make_pair(mknary(e->op(), args.begin(), args.end()), didrepl);
  }
  Expr replaceOne(Expr e, Expr from, Expr to)
  { return _replaceOne(e, from, to).first; }

  template <typename Range>
  void nonuniqfilter(const Expr& e, const std::function<int(Expr)>& filt,
    Range& vec)
  {
    if (isOpX<FDECL>(e))
      return;
    int ret = filt(e);
    if (ret)
      vec.insert(vec.end(), e);
    if (ret == 2)
      return;
    for (int i = 0; i < e->arity(); ++i)
      nonuniqfilter(e->arg(i), filt, vec);
  }

  typedef std::pair<Expr,int> NTDepth;
  // K: <NT, maxdepth>    V: list of output summaries
  typedef unordered_map<NTDepth,ExprVector> NTSummary;
  // K: input   V: Summary
  typedef unordered_map<Expr,NTSummary> NTSummaries;

  // Generalizes CEXs of Vx.lhs => rhs. Expects 'vars' to be FAPPs.
  Expr generalizeCEX(Expr lhs, Expr rhs, Expr negrhs, const ExprVector &vars)
  {
    ZSolver<EZ3>::Model *m = NULL;
    ExprVector tocheck;
    // TODO: Better method of generating CEXs
    static const int NUM_MODELS = 3;
    tocheck.resize(2 + NUM_MODELS, mk<TRUE>(efac));
    tocheck[NUM_MODELS] = lhs;
    tocheck[NUM_MODELS + 1] = negrhs;
    ExprVector model(vars.size());
    for (int i = 0; i < NUM_MODELS; ++i)
    {
      tribool res = u.isSat(tocheck);
      if (!res)
        break;
      m = u.getModelPtr();
      assert(m);
      int j = 0;
      for (const Expr &var : vars)
        model[j++] = mk<EQ>(var, m->eval(var));
      tocheck[i] = mk<NEG>(conjoin(model, efac));
    }
    tocheck.resize(NUM_MODELS);
    for (int i = 0; i < NUM_MODELS; ++i)
      if (!isOpX<TRUE>(tocheck[i]))
        tocheck[i] = tocheck[i]->left();
    // TODO: Use OpenSMT ITP
    return getItp(disjoin(tocheck, efac), mk<AND>(lhs, rhs), vars);
  }

  // K: assumptions (K: hole,  V: formula),  V: function
  typedef pair<ExprUMap,Expr> SynthPred;
  pair<ExprVector,unordered_map<Expr,vector<const SynthPred*>>> weakenClasses(Expr nt,
    Expr input, const ExprUSet &vars, const ExprUSet &holes,
    const vector<SynthPred>& funcs)
  {
    wsolver.reset();
    wsolver.assertExpr(input);
    // First, partition by variables
    // K: vars    V: list of <new func, old func>
    unordered_map<ExprSet,vector<std::pair<Expr,const SynthPred*>>> partitions;
    auto isvar = [&] (Expr e) -> int {
      // TODO: Should we split x and -x? What if we can't detect?
      return (vars.count(e) || (isOpX<UN_MINUS>(e) && vars.count(e->left()))) ? 2:0;
    };
    int nhole = 0;
    for (const SynthPred &func : funcs)
    {
      Expr out = func.second;
      const auto& assms = func.first;
      assert(isOpX<EQ>(out));
      assert(out->left() == nt);

      ExprSet thisvars;
      Expr newout = EvalPred(u, assms, out->right(), nt);
      nonuniqfilter(newout, isvar, thisvars);
      /*for (const Expr &hole : holes)
        if (assms.count(hole) != 0)
        {
          filter(assms.at(hole), isvar, inserter(thisvars, thisvars.end()));
          Expr newhole = mkConst(
            mkTerm(string("hole@")+to_string(nhole++), efac), typeOf(hole));
          Expr newassm = replaceAll(assms.at(hole), hole, newhole);
          newpred.first[newhole] = newassm;
          wsolver.assertExpr(newassm);
          newpred.second = replaceAll(newpred.second, hole, newhole);
        }*/
      partitions[thisvars].emplace_back(newout, &func);
    }
    wsolver.push();
    ExprVector out;
    unordered_map<Expr,vector<const SynthPred*>> out2;
    for (const auto &vars_funcs : partitions)
    {
      if (vars_funcs.second.size() == 1)
      {
        // Only one function, just use it.
        out.push_back(vars_funcs.second[0].first);
        out2[out.back()].push_back(vars_funcs.second[0].second);
        continue;
      }

      vector<vector<std::pair<Expr,const SynthPred*>>> subparts{vars_funcs.second};

      for (int i = 0; i < subparts.size(); ++i)
      {
        Expr max = subparts[i][0].first, min = max;
        for (auto &funcpair : subparts[i])
        {
          if (!funcpair.first) continue;
          const Expr &func = funcpair.first;
          wsolver.assertExpr(mk<GT>(
            func->left()->right(), min->left()->right()));
          if (!wsolver.solve())
            min = func;
          /*else
          {
            wsolver.pop(); wsolver.push();
            wsolver.assertExpr(mk<LT>(
              func->left()->right(), min->left()->right()));
            if (wsolver.solve())
            {
              if (i + 1 == subparts.size())
                subparts.resize(subparts.size() + 1);
              subparts[i+1].push_back(funcpair);
              funcpair.first = NULL; funcpair.second = NULL;
            }
          }*/
          wsolver.pop(); wsolver.push();
          wsolver.assertExpr(mk<LT>(
            func->right()->right(), max->right()->right()));
          if (!wsolver.solve())
            max = func;
          /*else
          {
            wsolver.pop(); wsolver.push();
            wsolver.assertExpr(mk<GT>(
              func->right()->right(), max->right()->right()));
            if (wsolver.solve())
            {
              if (i + 1 == subparts.size())
                subparts.resize(subparts.size() + 1);
              subparts[i+1].push_back(funcpair);
              funcpair.first = NULL; funcpair.second = NULL;
            }
          }*/
          wsolver.pop(); wsolver.push();
        }
        assert(isOpX<AND>(min)); assert(isOpX<AND>(max));
        assert(isOpX<GEQ>(min->left())); assert(isOpX<GEQ>(max->left()));
        assert(isOpX<LEQ>(min->right())); assert(isOpX<LEQ>(max->right()));
        Expr ret = mk<AND>(min->left(), max->right());
        for (const auto &funcpair : subparts[i])
        {
          if (!funcpair.first) continue;
          out2[ret].push_back(funcpair.second);
        }
        out.push_back(ret);
        wsolver.assertExpr(mk<NEG>(ret));
        wsolver.push();
        for (const auto &funcpair : subparts[i])
        {
          if (!funcpair.first) continue;
          wsolver.assertExpr(funcpair.first);
          assert(!wsolver.solve());
          wsolver.pop(); wsolver.push();
        }
      }
    }
    return make_pair(std::move(out), std::move(out2));
  }

  Expr mkhole(Expr nt, int i)
  {
    return mkConst(
      mkTerm(getTerm<string>(nt->left()->left())+"@"+to_string(i), nt->efac()),
      nt->left()->last());
  }

  public:

  PruningSolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) : BaseSolver(_prob, _efac, _z3, p), wsolver(_z3) {}

  virtual tribool Solve()
  {
    if (prob.synthfuncs.size() > 1)
    {
      _errmsg = "Pruning solver currently doesn't work for more than one function";
      return indeterminate;
    }
    if (prob.singleapps.size() != prob.synthfuncs.size())
    {
      _errmsg = "Pruning solver currently doesn't work for non-single-application functions";
      return indeterminate;
    }

    const SynthFunc& func = prob.synthfuncs[0];
    ExprVector funcvars(func.vars.size());
    for (int i = 0; i < func.vars.size(); ++i) funcvars[i] = fapp(func.vars[i]);
    ExprUSet funcvarsset(funcvars.begin(), funcvars.end());
    Grammar& gram = (Grammar&)func.gram;
    if (!func.hasgram)
    {
      _errmsg = "Pruning solver currently doesn't work without a grammar given";
      return indeterminate;
    }
    if (gram.nts.size() > 1)
    {
      _errmsg = "Pruning solver currently doesn't work for grammars with more than one non-terminal";
      return indeterminate;
    }

    // We'll eventually need to transform the productions like this, so do now
    vector<std::tuple<Expr,Expr,ExprVector>> prods;
    ExprUSet allholes;
    for (const Expr& prod : gram.prods.at(gram.root))
    {
      Expr newprod = prod;
      ExprVector roots;
      nonuniqfilter(prod, [&](Expr e){return e == gram.root;}, roots);
      for (int i = 0; i < roots.size(); ++i)
      {
        roots[i] = mkConst(
          mkTerm(getTerm<string>(roots[i]->left()->left()) + to_string(i), efac),
          roots[i]->left()->last());
        newprod = replaceOne(newprod, gram.root, roots[i]);
        allholes.insert(roots[i]);
      }
      prods.emplace_back(prod, newprod, std::move(roots));
    }

    /*Expr newout = mkConst(mkTerm(string("newout"), efac), typeOf(gram.root));
    Expr newout_spec = replaceAll(allcons,
      prob.singleapps.begin()->second, newout);
    Expr newout_notspec = mkNeg(newout_spec);*/
    Expr root_spec = replaceAll(allcons,
      prob.singleapps.begin()->second, gram.root);
    Expr root_notspec = mkNeg(root_spec);

    Expr zero = mkTerm(mpz_class(0), efac), one = mkTerm(mpz_class(1), efac),
         etrue = mk<TRUE>(efac), efalse = mk<FALSE>(efac);

    NTSummaries summ;

    unordered_map<Expr,Grammar> btgram; // K: input
    unordered_map<Expr,GramEnum> btenum; // K: input
    unordered_map<Expr,ExprUMap> btnt_to_eqc; // K: input
    ZSolver<EZ3> btsolver(z3);

    TravParams tparams; tparams.SetDefaults();
    tparams.method = TPMethod::NEWTRAV; tparams.type = TPType::ORDERED;
    tparams.maxrecdepth = 0;
    tparams.iterdeepen = false; tparams.simplify = true;
    tparams.prune = true; tparams.enumnts = true;

    // Generate initial input sets

    ExprVector disjs;
    u.flatten(root_spec, disjs, true, funcvars,
      keepQuantifiersRepl);

    ExprVector allpositive;
    for (const Expr& var : funcvars) allpositive.push_back(mk<GEQ>(var, zero));
    allpositive.push_back(NULL);
    if (allpositive.size() > 1)
      for (Expr& d : disjs)
      {
        allpositive.back() = d;
        d = mknary<AND>(allpositive);
      }

    for (const Expr &in : disjs)
    {
      summ[in][make_pair(gram.root, -1)] = ExprVector{mk<FALSE>(efac)};
      auto btppfn = [&] (const Expr &prod, const TravContext &ctx,
        const Expr &hole, const Expr &nt, int depth) -> tribool {
        tribool ret = false;
        if (btnt_to_eqc[in].count(nt) == 0)
          return false;
        btsolver.reset();
        btsolver.assertExpr(in);
        for (const auto& hole_nt : ctx.holes)
          btsolver.assertExpr(replaceAll(btnt_to_eqc[in][hole_nt.second.first],
            gram.root, hole_nt.first));
        btsolver.assertExpr(mk<EQ>(gram.root, ctx.holeyCtx));
        btsolver.assertExpr(root_spec);
        if (!btsolver.solve())
          return true;
        return ret;
      };
      auto btpafn = [&] (const Expr &oper, const vector<ParseTree> &args,
        const TravContext &ctx, const Expr &hole, const Expr &nt, int depth) {
        PruneRetType ret;
        int b = 0;
        if (ctx.holes.size() > 0)
          get<2>(ret) = skipcand;
        return ret;
      };

      btenum.emplace(in, GramEnum(btgram[in], NULL, btppfn, params.debug));
      btgram[in].setRoot(gram.root);
      for (const Expr& var : funcvars)
        btgram[in].addVar(var);
      btenum.at(in).SetPAFn(btpafn);
    }
    for (int maxdepth = 0; true; ++maxdepth)
    {
      bool backtrack = false;
      const auto thiskey = make_pair(gram.root, maxdepth);
      for (const auto& i_summ : summ)
      {
        const Expr& input = i_summ.first;
        const ExprVector& prevsumm = i_summ.second.at(make_pair(gram.root, maxdepth - 1));
        // Enumerate productions
        vector<SynthPred> funcs;
        for (const auto& prod_holes : prods)
        {
          const Expr &prod = get<0>(prod_holes);
          const Expr &holeyprod = get<1>(prod_holes);
          const ExprVector &holes = get<2>(prod_holes);
          if (maxdepth == 0 && gram.isRecursive(prod, gram.root))
            continue;
          ExprUMap assms;
          /*Expr allout = disjoin(prevsumm, efac);
          for (const Expr& hole : holes)
            tocheck.push_back(replaceAll(allout, gram.root, hole));
          tocheck.push_back(mk<EQ>(newout, holeyprod));
          tocheck.push_back(newout_notspec);
          tribool res = u.isSat(tocheck);
          if (!res)
          {
            assert(0 && "Checking possible solution unimplemented");
          }
          if (indeterminate(res))
            // TODO: What to do if indeterminate?
            assert(0 && "PruneTrav can't handle unknowns");*/
          function<void(int)> perm = [&] (int pos)
          {
            if (pos == holes.size())
            {
              funcs.emplace_back(assms, mk<EQ>(gram.root, holeyprod));
              return;
            }
            for (const Expr& out : prevsumm)
            {
              Expr assm = replaceAll(out, gram.root, holes[pos]);
              assms[holes[pos]] = assm;
              perm(pos + 1);
            }
          };
          perm(0);
          // Won't work
          /*tocheck.pop_back();
          Expr func = eliminateQuantifiers(conjoin(tocheck), _qvars);
          assert(!isOpX<FALSE>(func));
          if (isOpX<AND>(func))
            func = func->last();
          func = func->right();
          funcs.push_back(func);*/
        }

        // Generate (weaker) equivalence classes
        auto eqclasses = weakenClasses(gram.root, input, funcvarsset, allholes, funcs);

        // Fill grammar
        Grammar &ig = btgram[input];
        for (int i = 0; i < eqclasses.first.size(); ++i)
        {
          Expr eqcnt = ig.addNt(string("eq")+to_string(i)+"@"+to_string(maxdepth), gram.root->left()->last());
          ig.addProd(mkhole(gram.root, maxdepth), eqcnt);
          for (const auto &func : eqclasses.second[eqclasses.first[i]])
          {
            Expr prod = func->second->right();
            for (const auto &hole_assm : func->first)
            {
              int eqc = 0;
              for (; eqc < prevsumm.size(); ++eqc)
                if (prevsumm[eqc] == replaceAll(hole_assm.second,
                hole_assm.first, gram.root))
                  break;
              prod = replaceAll(prod, hole_assm.first, 
                ig.addNt(string("eq")+to_string(eqc)+"@"+to_string(maxdepth-1),
                  gram.root->left()->last()));
            }
            ig.addProd(eqcnt, prod);
            btnt_to_eqc[input][eqcnt] = eqclasses.first[i];
          }
        }

        summ[input][thiskey] = eqclasses.first;
      }

      // Fix input

      ExprVector checkdisjs(2), asserts(3);
      checkdisjs[0] = root_notspec;
      asserts[0] = etrue;

      int numsumms = summ.begin()->second[thiskey].size();
      for (int i = 0; i < numsumms; ++i)
      {
        ExprVector eqc;
        bool good = false;
        for (const auto &i_summ : summ)
        {
          Expr in = i_summ.first;
          Expr out = i_summ.second.at(thiskey)[i];
          asserts[0] = in; asserts[1] = out; asserts[2] = root_spec;
          if (!u.isSat(asserts))
          {
            // Already good, nothing to do
            good = true;
            break;
          }

          checkdisjs[1] = mk<NEG>(out);
          asserts[1] = mk<FORALL>(gram.root->left(),mknary<OR>(checkdisjs));
          asserts[2] = etrue;
          if (!u.isSat(asserts))
          {
            // No strengthening exists, try next input
            eqc.push_back(mk<IMPL>(in, out));
            continue;
          }
          // Strengthen
          Expr newconj =
            //generalizeCEX(mk<AND>(in, out), root_spec, funcvars);
            generalizeCEX(in, mk<NEG>(asserts[1]->last()), asserts[1], funcvars);
          assert(newconj);
          ExprVector newin;
          if (!isOpX<AND>(newconj))
            newin.push_back(newconj);
          else
            newin.insert(newin.end(), newconj->args_begin(), newconj->args_end());
          if (!isOpX<AND>(in))
            newin.push_back(in);
          else
            newin.insert(newin.end(), in->args_begin(), in->args_end());

          auto tmp = std::move(i_summ.second);
          summ.erase(in);
          summ[mknary<AND>(newin)] = std::move(tmp);
          good = true;
          break;
        }
        if (good)
          continue;

        for (const auto &i_summ : summ)
        {
          Expr in = i_summ.first;
          ExprVector probs;

          tparams.maxrecdepth = maxdepth;
          Grammar &ig = btgram.at(in);

          if (ig.prods.count(gram.root) != 0)
          {
            assert(ig.prods.at(gram.root).size() == 1);
            ig.delProd(gram.root, ig.prods.at(gram.root)[0]);
          }
          ig.addProd(gram.root, mkhole(gram.root, maxdepth));

          GramEnum &ie = btenum.at(in);
          ie.SetParams(tparams, NTParamMap());
          ie.Restart();
          while (!ie.IsDone())
          {
            Expr ret = ie.Increment();
            if (ret && !ig.isNt(ret))
              probs.push_back(ret);
          }
          DefMap cands;
          for (const Expr &p : probs)
          {
            ExprVector holes;
            filter(p, [&](Expr e){return ig.isNt(e);},
              inserter(holes, holes.begin()));
            if (holes.size() == 0)
            {
              cands[&func] = p;
              if (checkCands(cands))
              {
                _foundfuncs = cands;
                if (params.debug)
                  errs() << "Candidate found at recursion depth " <<
                    maxdepth << endl;
                return true;
              }
            }
          }
        }

        assert(0 && "Adding new inputs unimplemented");

        asserts[0] = etrue;
        asserts[2] = etrue;
        for (const auto &i_summ : summ)
        {
          checkdisjs[1] = mk<NEG>(i_summ.second.at(thiskey)[i]);
          asserts[1] = mk<FORALL>(gram.root->left(),mknary<OR>(checkdisjs));
          tribool res = u.isSat(asserts);
          if (!res)
          {
            assert(0 && "Checking possible solution unimplemented");
          }
          // TODO: What to do if indeterminate?
          //else if (indeterminate(res))
            //assert(0 && "PruneTrav can't handle unknowns");
        }
        /*
         * Problem: we have per-input summaries, but now we want a new input.
         *   In order to do so, we need to know what the NT is at some new input,
         *   but we don't know.
         * TODO: Resolve somehow.

        // Generate new input
        Expr newin = generalizeCEX(conjoin(eqc, efac), root_spec, funcvars);
        if (summ.size() == 1 && isOpX<TRUE>(summ.begin()->first))
        {
          auto tmp = std::move(summ.begin()->second);
          summ.erase(summ.begin());
          summ[newin] = std::move(tmp);
        }
        else
        {
          for (int i = -1; i < maxdepth; ++i)
            summ[newin][make_pair(gram.root, i)] = ExprVector{mk<FALSE>(efac)};
        }
        backtrack = true;
        break;
        */
      }

      if (backtrack)
      {
        // Backtrack
        maxdepth = -1;
        continue;
      }

      if (params.debug)
        outs() << "Done with depth " << maxdepth << endl;
    }
  }
};

}

#endif
