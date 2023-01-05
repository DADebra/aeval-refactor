#ifndef __PRUNINGSOLVER_HPP__
#define __PRUNINGSOLVER_HPP__


#include "sygus/BaseSolver.hpp"
#include "sygus/ExprNorm.hpp"
#include "sygus/ExprEval.hpp"
#include "utils/SetHash.hpp"
#include "utils/Mat.hpp"
#include "utils/Misc.hpp"

namespace ufo
{
using namespace std;
using namespace boost;

class PruningSolver : public BaseSolver
{
  private:
  typedef pair<ExprUMap,Expr> SynthPred;
  typedef std::pair<Expr,int> NTDepth;
  // K: <NT, maxdepth>    V: list of output summaries
  typedef unordered_map<NTDepth,ExprVector> NTSummary;
  // K: input   V: Summary
  typedef vector<std::pair<Expr,std::shared_ptr<NTSummary>>> NTSummaries;

  struct Problem
  {
    Expr in;
    Expr cause;
    ExprUMap assms;

    Problem(Expr _in, Expr _cause, const ExprUMap &_h) :
      in(_in), cause(_cause), assms(_h) {}
  };
  typedef std::pair<int,int> EqcDepth;

  Expr ezero = mkTerm(mpz_class(0), efac), eone = mkTerm(mpz_class(1), efac),
       enegone = mkTerm(mpz_class(-1), efac),
       etrue = mk<TRUE>(efac), efalse = mk<FALSE>(efac);

  Expr root_spec, root_notspec;

  NTSummaries summ;
  unordered_map<const NTSummary*,Grammar> btgram; // K: summary
  unordered_map<const NTSummary*,GramEnum> btenum; // K: summary
  unordered_map<const NTSummary*,ExprUMap> btnt_to_summ; // K: summary
  unordered_map<const NTSummary*,unordered_map<Expr,std::pair<NTDepth,int>>>
    btnt_to_eqc; // K: summ, V: { K: btgram.NT, V: <NT,depth,eq_num> }
  unordered_map<const NTSummary*,ZSolver<EZ3>> btsolver;
  unordered_map<const NTSummary*,Expr> summ_to_in; // K: summ, V: in
  unordered_map<EqcDepth,vector<Problem>> refine_probs, newin_probs;
  // K: <btnt, ctx>, V: {prod}
  unordered_map<std::pair<Expr,WithExtra<Expr,ExprUMap,false>>,ExprUSet>
    needrefine;

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
    int foundmodels = 0;
    for (int i = 0; i < NUM_MODELS; ++i)
    {
      tribool res = u.isSat(tocheck);
      if (!res)
        break;
      foundmodels++;
      m = u.getModelPtr();
      assert(m);
      int j = 0;
      for (const Expr &var : vars)
        model[j++] = mk<EQ>(var, m->eval(var));
      tocheck[i] = mk<NEG>(conjoin(model, efac));
    }
    tocheck.resize(foundmodels);
    for (int i = 0; i < foundmodels; ++i)
      if (!isOpX<TRUE>(tocheck[i]))
        tocheck[i] = tocheck[i]->left();
    // TODO: Use OpenSMT ITP
    Expr allmodels = disjoin(tocheck, efac);
    Expr ret = getItp(allmodels, mk<AND>(lhs, rhs), vars);
    if (!ret)
      return std::move(allmodels);
    return std::move(ret);
  }

  Expr mkonecomb(const mat::Mat<mpq_class> &coefs, const ExprVector &vars)
  {
    assert(coefs.n_elem == vars.size());
    ExprVector ret;
    for (int i = 0; i < vars.size(); ++i)
      ret.push_back(mk<MULT>(
        mkTerm(coefs[i].get_num(), vars[i]->efac()), vars[i]));
    return plusjoin(ret);
  }

  Expr mkcomb(mat::Mat<mpq_class> &sol, const ExprVector &vars)
  {
    assert(sol.n_cols == vars.size() + 1);
    ExprVector ret;
    for (int r = 0; r < sol.n_rows; ++r)
    {
      ExprVector comb;
      int i = 0;
      for (; i < vars.size(); ++i)
        comb.push_back(mk<MULT>(
          mkTerm(sol(r,i).get_num(), vars[i]->efac()), vars[i]));
      ret.push_back(mk<EQ>(
        plusjoin(comb), mkTerm(sol(r, i).get_num(), vars[0]->efac())));
    }
    return conjoin(ret, vars[0]->efac());
  }

  Expr mkonecomb(const ExprVector &coefs, const ExprVector &vars)
  {
    assert(coefs.size() == vars.size());
    ExprVector ret;
    for (int i = 0; i < vars.size(); ++i)
      ret.push_back(mk<MULT>(coefs[i], vars[i]));
    return plusjoin(ret);
  }

  // Collapses to convex hull (but in diff format) if coefs not linearly related
  Expr nonlinHull(const vector<WithExtra<Expr,const SynthPred*>>& funcs,
    const ExprUSet &vars, const Expr &nt)
  {
    Expr min, max;
    ExprVector vvars(vars.size() + 1);
    mat::Mat<mpq_class> lcoefmat(funcs.size(), vars.size() + 2, mat::fill::zeros);
    lcoefmat.col(0) = 1;
    mat::Mat<mpq_class> ucoefmat(funcs.size(), vars.size() + 2, mat::fill::zeros);
    ucoefmat.col(0) = 1;
    mat::Col<mpq_class> zerovec(funcs.size(), mat::fill::zeros);
    mat::Col<mpq_class> onevec(funcs.size(), mat::fill::ones);
    for (int r = 0; r < funcs.size(); ++r)
    {
      Expr lbound = normalizeLIA(funcs[r].obj->left()->right(), vars),
           ubound = normalizeLIA(funcs[r].obj->right()->right(), vars);
      assert(lbound->arity() == vars.size() + 1);
      assert(ubound->arity() == vars.size() + 1);
      for (int c = 0; c < lbound->arity(); ++c)
      {
        if (!vvars[c]) vvars[c] = lbound->arg(c)->right();
        else assert(vvars[c] == lbound->arg(c)->right());
        lcoefmat(r, c+1) = getTerm<mpz_class>(lbound->arg(c)->left());
      }
      for (int c = 0; c < ubound->arity(); ++c)
      {
        if (!vvars[c]) vvars[c] = ubound->arg(c)->right();
        else assert(vvars[c] == ubound->arg(c)->right());
        ucoefmat(r, c+1) = getTerm<mpz_class>(ubound->arg(c)->left());
      }
    }
    ExprVector lvars, uvars;
    for (const Expr &var : vvars)
    {
      const string &name = isOpX<FAPP>(var) ?
        getTerm<string>(var->left()->left()) : "_c";
      lvars.push_back(mkConst(mkTerm(name + "cl", var->efac()), typeOf(var)));
      uvars.push_back(mkConst(mkTerm(name + "cu", var->efac()), typeOf(var)));
    }
    mat::Mat<mpq_class> sol;
    bool solveret = mat::solvecomb<mpq_class>(sol, lcoefmat);
    if (solveret)
    {
      /*sol = sol.t();
      min = mk<AND>(
        mkcomb(sol, lvars),
        mk<GEQ>(nt, mkonecomb(lvars, vvars)));*/
    }
    else
    {
      /*sol = mat::min(lcoefmat, 0);
      min = mk<AND>(mk<GEQ>(nt, mkonecomb(sol, vvars)));*/
    }
    solveret = mat::solvecomb<mpq_class>(sol, ucoefmat);
    if (solveret)
    {
      /*sol = sol.t();
      max = mk<AND>(
        mkcomb(sol, uvars),
        mk<LEQ>(nt, mkonecomb(uvars, vvars)));*/
    }
    else
    {
      /*sol = mat::max(ucoefmat, 0);
      max = mk<AND>(mk<LEQ>(nt, mkonecomb(sol, vvars)));*/
    }

    ExprVector ret;
    /*ret.insert(ret.end(), min->args_begin(), min->args_end());
    ret.insert(ret.end(), max->args_begin(), max->args_end());*/
    return conjoin(ret, efac);
  }

  // K: assumptions (K: hole,  V: formula),  V: function
  pair<ExprVector,unordered_map<Expr,vector<const SynthPred*>>> weakenClasses(Expr nt,
    Expr input, const ExprUSet &vars, const ExprUSet &holes,
    const vector<SynthPred>& funcs)
  {
    wsolver.reset();
    wsolver.assertExpr(input);
    // First, partition by variables
    // K: vars    V: list of <new func, old func>
    unordered_map<ExprSet,vector<WithExtra<Expr,const SynthPred*>>> partitions;
    auto isvar = [&] (Expr e) -> bool {
      //return (vars.count(e) || (isOpX<UN_MINUS>(e) && vars.count(e->left()))) ? 2:0;
      return vars.count(e) != 0;
    };
    int nhole = 0;
    for (const SynthPred &func : funcs)
    {
      Expr out = func.second;
      const auto& assms = func.first;
      assert(isOpX<EQ>(out));
      assert(out->left() == nt);

      ExprSet thisvars;
      ExprVector newoutv = EvalPred(u, assms, out->right(), nt, vars);
      for (const Expr& newout : newoutv)
      {
        assert(isOpX<AND>(newout));
        Expr normout = mk<AND>(
          mk<GEQ>(nt, normalizeLIA(newout->left()->right(), vars)),
          mk<LEQ>(nt, normalizeLIA(newout->right()->right(), vars)));
        for (const Expr& conj : *normout)
          for (const Expr& arg : *conj->right())
            if (getTerm<mpz_class>(arg->left()) != 0 && arg->right() != eone)
              thisvars.insert(arg->right());
        /*Expr normout = newout;
        filter(normout, isvar, inserter(thisvars, thisvars.end()));*/
        partitions[thisvars].emplace_back(normout, &func);
        thisvars.clear();
      }
    }

    wsolver.push();
    ExprVector out;
    unordered_map<Expr,vector<const SynthPred*>> out2;
    for (const auto &vars_funcs : partitions)
    {
      if (vars_funcs.second.size() == 1)
      {
        // Only one function, just use it.
        Expr func = vars_funcs.second[0].obj;
        Expr ret = mk<AND>(
          mk<GEQ>(nt, normalizeLIA(func->left()->right(), vars)),
          mk<LEQ>(nt, normalizeLIA(func->right()->right(), vars)));
        out.push_back(ret);
        out2[out.back()].push_back(vars_funcs.second[0].extra);
        continue;
      }

      vector<vector<WithExtra<Expr,const SynthPred*>>> subparts{vars_funcs.second};

      for (int i = 0; i < subparts.size(); ++i)
      {
        /*Expr max = subparts[i][0].first, min = max;
        for (auto &funcpair : subparts[i])
        {
          if (!funcpair.first) continue;
          const Expr &func = funcpair.first;
          wsolver.assertExpr(mk<GT>(
            func->left()->right(), min->left()->right()));
          if (!wsolver.solve())
            min = func;
          \*else
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
          }*\
          wsolver.pop(); wsolver.push();
          wsolver.assertExpr(mk<LT>(
            func->right()->right(), max->right()->right()));
          if (!wsolver.solve())
            max = func;
          \*else
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
          }*\
          wsolver.pop(); wsolver.push();
        }
        assert(isOpX<AND>(min)); assert(isOpX<AND>(max));
        assert(isOpX<GEQ>(min->left())); assert(isOpX<GEQ>(max->left()));
        assert(isOpX<LEQ>(min->right())); assert(isOpX<LEQ>(max->right()));
        Expr ret = mk<AND>(min->left(), max->right());*/
        Expr ret = convexHull(subparts[i].begin(), subparts[i].end(), vars, nt);
        Expr nonlinret = nonlinHull(subparts[i], vars, nt);
        for (const auto &funcpair : subparts[i])
        {
          if (!funcpair.obj) continue;
          out2[ret].push_back(funcpair.extra);
        }
        out.push_back(ret);
        wsolver.assertExpr(mk<NEG>(ret));
        wsolver.push();
        for (const auto &funcpair : subparts[i])
        {
          if (!funcpair.obj) continue;
          wsolver.assertExpr(funcpair.obj);
          assert(!wsolver.solve());
          wsolver.pop(); wsolver.push();
        }
      }
    }
    return make_pair(std::move(out), std::move(out2));
  }

  inline Expr mkhole(Expr nt, int i)
  {
    return mkConst(
      mkTerm(getTerm<string>(nt->left()->left())+"@"+to_string(i), nt->efac()),
      nt->left()->last());
  }

  inline Expr mkeqc(int num, int depth, Expr type)
  {
    return mkConst(
      mkTerm(string("eq")+to_string(num)+"@"+to_string(depth), type->efac()),
      type);
  }

  void addInput(Expr in, Expr gnt, const ExprVector& vars)
  {
    summ.emplace_back(in, new NTSummary());
    (*summ.back().second)[make_pair(gnt, -1)] = ExprVector{efalse};
    const NTSummary *thissumm = summ.back().second.get();
    summ_to_in[thissumm] = in;
    btsolver.emplace(thissumm, z3);
    btsolver.at(thissumm).assertExpr(root_spec);
    auto btppfn = [&,thissumm,gnt] (const Expr &prod, const TravContext &ctx,
      const Expr &hole, const Expr &btnt, int depth, const TravContext &checkctx) -> tribool {
      auto &thisntmap = btnt_to_summ[thissumm];
      auto &thissolver = btsolver.at(thissumm);
      if (thisntmap.count(btnt) == 0)
        return false;
      //checkconjs.clear();
      /*faArgs.clear();
      faArgs.push_back(gram.root->left());*/
      ExprUMap assms;
      thissolver.push();
      thissolver.assertExpr(summ_to_in[thissumm]);
      for (const auto& hole_nt : checkctx.holes)
      {
        if (hole_nt.first == hole)
          continue;
        //faArgs.push_back(hole_nt.first->left());
        Expr assm = replaceAll(thisntmap[hole_nt.second.nt],
          gnt, hole_nt.first);
        assms[hole_nt.first] = assm;
        /*checkconjs.push_back(*/thissolver.assertExpr(assm);
        //thissolver.assertExpr(checkconjs.back());
      }
      /*thissolver.push();
      thissolver.assertExpr(root_spec);*/
      Expr eqctx = mk<EQ>(gnt, checkctx.holeyCtx);
      /*checkconjs.push_back(*/thissolver.assertExpr(eqctx);
      //thissolver.assertExpr(checkconjs.back());
      tribool ret = thissolver.solve();
      thissolver.pop();
      if (!ret)
      {
        auto refret = needrefine[make_pair(btnt, WithExtra<Expr,ExprUMap,false>(ctx.holeyCtx, assms))]
          .emplace(prod);
        assert(refret.second);
        return true;
      }
      // I'm fairly confident it's impossible to need to strengthen here
      /*auto eqc_pair = btnt_to_eqc.at(thissumm).at(nt);
      thissolver.pop();
      checkdisjs[1] = mk<NEG>(conjoin(checkconjs, nt->efac()));
      faArgs.push_back(mknary<OR>(checkdisjs));
      Expr tocheck = mknary<FORALL>(faArgs);
      thissolver.assertExpr(tocheck);
      ret = thissolver.solve();
      if (ret)
      {
        // Can strengthen
        btprobs.emplace_back(eqc_pair.second, eqc_pair.first.second,
          summ_to_in[thissumm], replaceAll(ctx.holeyCtx, ctx.holes), STREN);
        return true;
      }*/
      return false;
    };
    auto btpafn = [&,thissumm,gnt] (const Expr &oper,const vector<ParseTree> &args,
      const TravContext &ctx, const Expr &hole, const Expr &btnt, int depth,
      int min) {
      PruneRetType ret;
      ExprVector holes;
      filter(hole, [&](Expr e){return ctx.holes.count(e) != 0;},
        inserter(holes, holes.end()));
      if (holes.size() != 0)
        get<2>(ret) = skipcand;
      /*for (int i = 0; i < args.size(); ++i)
        if (ctx.holes.count(args[i].toSortedExpr()) != 0)
          get<2>(ret) = skipcand;*/
      auto &thisntmap = btnt_to_summ[thissumm];
      if (thisntmap.count(btnt) == 0)
        return ret;
      auto &thissolver = btsolver.at(thissumm);
      thissolver.push();
      thissolver.assertExpr(summ_to_in[thissumm]);
      for (const auto& hole_nt : ctx.holes)
        thissolver.assertExpr(replaceAll(
          thisntmap[hole_nt.second.nt],
          gnt, hole_nt.first));
      thissolver.assertExpr(mk<EQ>(gnt, ctx.holeyCtx));
      tribool solveret = thissolver.solve();
      thissolver.pop();
      if (!solveret)
      {
        for (int i = 0; i < args.size(); ++i)
        {
          if (i >= min && ctx.holes.count(args[i].toSortedExpr()) == 0)
            get<0>(ret).push_back(i);
          else
            get<1>(ret).push_back(i);
        }
        get<2>(ret) = skipcand;
      }
      return ret;
    };

    btenum.emplace(thissumm,
      GramEnum(btgram[thissumm], NULL, btppfn, 0));
    for (const Expr& var : vars)
      btgram[thissumm].addVar(var);
    btenum.at(thissumm).SetPAFn(btpafn);
  }

  ExprVector strendisjs, strenasserts;
  inline bool canStrengthen(Expr in, Expr summ, Expr nt)
  {
    strendisjs[1] = mk<NEG>(summ);
    strenasserts[0] = in;
    strenasserts[1] = mk<FORALL>(nt->left(), mknary<OR>(strendisjs));
    return bool(u.isSat(strenasserts));
  }

  ExprVector stFaArgs; ExprVector stCheckConjs;
  inline bool canStrengthenAssm(Expr in, Expr summ, Expr nt,
    const ExprUMap& assms)
  {
    stFaArgs.clear();
    stFaArgs.reserve(assms.size() + 1);
    stCheckConjs.clear();
    stCheckConjs.reserve(assms.size() + 1);
    for (const auto& nt_as : assms)
    {
      stFaArgs.push_back(nt_as.first);
      stCheckConjs.push_back(nt_as.second);
    }
    stFaArgs.push_back(nt);
    stCheckConjs.push_back(root_spec);
    stFaArgs.push_back(mk<NEG>(conjoin(stCheckConjs, nt->efac())));
    Expr tocheck = mknary<FORALL>(stFaArgs);
    return bool(u.isSat(in, tocheck));
  }

  inline Expr strengthen(Expr in, Expr summ, Expr nt, const ExprVector& vars)
  {
    if (!canStrengthen(in, summ, nt))
      return NULL;
    Expr ret = generalizeCEX(in, mk<NEG>(strenasserts[1]->last()),
      strenasserts[1], vars);
    assert(ret);
    ExprVector newin;
    if (!isOpX<AND>(ret))
      newin.push_back(ret);
    else
      newin.insert(newin.end(), ret->args_begin(), ret->args_end());
    if (!isOpX<AND>(in))
      newin.push_back(in);
    else
      newin.insert(newin.end(), in->args_begin(), in->args_end());
    return simplifyBool(conjoin(newin, efac));
  }

  ExprVector unrealasserts;
  inline bool isUnreal(Expr in, Expr summ)
  {
    unrealasserts[0] = in; unrealasserts[1] = summ;
    return bool(!u.isSat(unrealasserts));
  }

  ExprVector unrealassertsAs;
  inline bool isUnrealAssm(Expr in, Expr summ, const ExprUMap& assms)
  {
    unrealassertsAs.resize(1);
    unrealassertsAs.reserve(assms.size() + 2);
    for (const auto &nt_as : assms)
      unrealassertsAs.push_back(nt_as.second);
    unrealassertsAs.push_back(in);
    return bool(!u.isSat(unrealassertsAs));
  }

  public:

  PruningSolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) : BaseSolver(_prob, _efac, _z3, p), wsolver(_z3)
  {
    strendisjs.resize(2);
    strenasserts.resize(2);
    unrealasserts.resize(3);
  }

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
    if (gram.graph().at(gram.root).size() > 1)
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

    root_spec = replaceAll(allcons,
      prob.singleapps.begin()->second, gram.root);
    root_notspec = mkNeg(root_spec);

    strendisjs[0] = root_notspec;
    unrealasserts[2] = root_spec;
    unrealassertsAs.push_back(root_spec);

    TravParams tparams; tparams.SetDefaults();
    tparams.method = TPMethod::NEWTRAV; tparams.type = TPType::STRIPED;
    tparams.maxrecdepth = 0;
    tparams.iterdeepen = false; tparams.simplify = true;
    tparams.prune = true; tparams.enumnts = true;

    // Generate initial input sets

    ExprVector disjs;
    u.flatten(root_spec, disjs, true, funcvars,
      keepQuantifiersRepl);

    ExprVector allpositive;
    for (const Expr& var : funcvars) allpositive.push_back(mk<GEQ>(var, ezero));
    allpositive.push_back(NULL);
    if (allpositive.size() > 1)
      for (Expr& d : disjs)
      {
        allpositive.back() = d;
        d = mknary<AND>(allpositive);
      }
    allpositive.back() = etrue;
    Expr eallpositive = conjoin(allpositive, efac);

    if (params.debug > 1)
      outs() << disjs.size() << " initial input sets";
    if (params.debug > 2)
    {
      outs() << ":";
      for (const Expr& in : disjs)
        outs() << "\n  " << in;
    }
    if (params.debug > 1)
      outs() << endl;

    for (const Expr &in : disjs)
    {
      addInput(in, gram.root, funcvars);
    }
    for (int maxdepth = 0; true; ++maxdepth)
    {
      if (params.debug)
        outs() << gram.root << " at depth " << maxdepth << ":" << endl;
      const auto thiskey = make_pair(gram.root, maxdepth);
      for (int j = 0; j < summ.size(); ++j)
      {
        const Expr& input = summ[j].first;
        const ExprVector& prevsumm = summ[j].second->at(make_pair(gram.root, maxdepth - 1));
        if (params.debug)
          outs() << "  Enumerating productions for input " << j << endl;
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
          assms[NULL] = input;
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
        }

        if (params.debug > 1)
          outs() << "    " << funcs.size() << " functions generated";
        if (params.debug > 2 && (funcs.size() < 16 || params.debug > 3))
        {
          outs() << ":";
          ExprVector evald;
          for (const SynthPred &func : funcs)
          {
            evald = EvalPred(u, func.first, func.second->right(), gram.root,
              funcvarsset);
            for (const Expr& e : evald)
              outs() << "\n      " << e;
          }
        }
        if (params.debug > 1)
          outs() << endl;

        // Generate (weaker) equivalence classes
        auto eqclasses = weakenClasses(gram.root, input, funcvarsset, allholes, funcs);

        if (params.debug > 1)
        {
          outs() << "    " << eqclasses.first.size() << " partitions: [ ";
          for (const auto &eqc_funcs : eqclasses.second)
            outs() << eqc_funcs.second.size() << " ";
          outs() << "]";
        }
        if (params.debug > 2)
        {
          outs() << ":";
          for (const Expr &eqc : eqclasses.first)
            outs() << "\n      " << eqc;
        }
        if (params.debug > 1)
          outs() << endl;

        // Fill grammar
        Grammar &ig = btgram[summ[j].second.get()];
        for (int i = 0; i < eqclasses.first.size(); ++i)
        {
          Expr eqcnt = ig.addNt(string("eq")+to_string(i)+"@"+to_string(maxdepth), gram.root->left()->last());
          //ig.addProd(mkhole(gram.root, maxdepth), eqcnt);
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
                ig.addNt(mkeqc(eqc, maxdepth-1, gram.root->left()->last())));
            }
            ig.addProd(eqcnt, prod);
            btnt_to_summ[summ[j].second.get()][eqcnt] = eqclasses.first[i];
            btnt_to_eqc[summ[j].second.get()][eqcnt] = make_pair(thiskey, i);
          }
        }

        (*summ[j].second)[thiskey] = eqclasses.first;
      }

      // Fix input

      bool backtrack = false;
      int numsumms = (*summ.begin()->second)[thiskey].size();
      if (params.debug)
        outs() << "  " << numsumms << " summaries" << endl;
      for (int i = 0; i < numsumms; ++i)
      {
        bool good = false;
        for (int j = 0; j < summ.size(); ++j)
        {
          auto &i_summ = summ[j];
          if (i_summ.second->count(thiskey) == 0)
            continue;
          Expr in = i_summ.first;
          Expr out = i_summ.second->at(thiskey)[i];
          if (isUnreal(in, out))
          {
            // Already good, nothing to do
            good = true;
            if (params.debug > 1)
              outs() << "    Class " << i << " OK" << endl;
            break;
          }

          // Strengthen
          Expr modin =
            strengthen(in, out, gram.root, funcvars);
          if (!modin)
            continue; // Can't strengthen

          if (params.debug > 1)
            outs() << "    Strengthening input " << j << " for Class " << i;
          if (params.debug > 2)
            outs() << ":\n      " << modin;
          if (params.debug > 1)
            outs() << endl;

          summ[j].first = modin;
          summ_to_in[i_summ.second.get()] = modin;
          good = true;
          break;
        }
        if (good)
          continue;

        if (params.debug > 1)
          outs() << "    Backtracking on Class " << i << ":" << endl;

        refine_probs.clear();
        newin_probs.clear();
        ExprUSet donesumms;
        int oldsummnum = summ.size();

        for (int j = 0; j < oldsummnum; ++j)
        {
          const auto& i_summ = summ[j];
          if (i_summ.second->count(thiskey) == 0)
            continue; // Can happen when we add a new input in a previous eqc
          if (!donesumms.insert(i_summ.second->at(thiskey)[i]).second)
            continue; // An eqc can be the same across several inputs

          Expr in = i_summ.first;
          Expr thiseqc = mkeqc(i, maxdepth, gram.root->left()->last());
          if (params.debug > 1)
            outs() << "      for input " << j << ":" << endl;

          tparams.maxrecdepth = maxdepth;
          Grammar &ig = btgram.at(i_summ.second.get());
          ig.setRoot(thiseqc);
          needrefine.clear();
          /*for (const Expr &nt : ig.nts)
            if (ig.pathExists(ig.root, nt))
              needrefine.emplace(nt, ExprUSet());
          needrefine.emplace(ig.root, ExprUSet());*/

          /*if (ig.prods.count(gram.root) != 0)
          {
            assert(ig.prods.at(gram.root).size() == 1);
            ig.delProd(gram.root, ig.prods.at(gram.root)[0]);
          }
          ig.addProd(gram.root, mkhole(gram.root, maxdepth));*/

          GramEnum &ie = btenum.at(i_summ.second.get());
          ie.SetParams(tparams, NTParamMap());
          ie.Restart();
          DefMap cands;
          while (!ie.IsDone())
          {
            Expr ret = ie.Increment();
            if (!ret || ig.isNt(ret))
              continue;
            ExprVector holes;
            filter(ret, [&](Expr e){return ig.isNt(e);},
              inserter(holes, holes.begin()));
            if (holes.size() == 0)
            {
              if (params.debug)
                outs() << "Candidate: " << ret << endl;
              cands[&func] = ret;
              if (checkCands(cands))
              {
                cands[&func] = ie.GetUnsimplifiedCand();
                _foundfuncs = cands;
                if (params.debug)
                  errs() << "Solution found at recursion depth " <<
                    maxdepth << endl;
                return true;
              }
              if (isUnreal(in, mk<EQ>(gram.root, ret)))
                refine_probs[make_pair(i,maxdepth)].emplace_back(Expr(), ret, ExprUMap());
              else
                newin_probs[make_pair(i,maxdepth)].emplace_back(Expr(), ret, ExprUMap());
            }
          }

          for (const auto &btnt_prods : needrefine)
          {
            const Expr& btnt = btnt_prods.first.first;
            const auto& ctx = btnt_prods.first.second;
            auto nt_eqc = btnt_to_eqc.at(i_summ.second.get()).at(btnt);
            /*for (const auto &ctx_holes : btnt_ctxs.second)
              btprobs[REFINE].emplace_back(eqc_pair.second,
                eqc_pair.first.second, in, ctx_holes.obj,
                std::move(ctx_holes.extra));*/
            if (btnt_prods.second.size() == ig.prods.at(btnt).size())
              refine_probs[make_pair(nt_eqc.second, nt_eqc.first.second)]
                .emplace_back(in, ctx.obj, ctx.extra);
          }
        }

        if (params.debug > 1 && (refine_probs.size() != 0 || newin_probs.size() != 0))
        {
          outs() << "    Problems found:\n";
          if (newin_probs.size() > 0)
            outs() << "      NEWIN: " << newin_probs.begin()->second.size() << "\n";
          else
            outs() << "      NEWIN: 0\n";
          outs() << "      REFINE: " << refine_probs.size() << endl;
        }

        for (const auto& eqc_probs : newin_probs)
          for (const Problem &prob : eqc_probs.second)
          {
            bool probgood = false;
            int strenin = -1;
            Expr out = mk<EQ>(gram.root, prob.cause);
            for (int j = oldsummnum; j < summ.size(); ++j)
            {
              if (isUnreal(summ[j].first, out))
              { probgood = true; break; }
              else if (canStrengthen(summ[j].first, out, gram.root))
              { strenin = j; break; }
            }
            if (probgood)
              continue;
            Expr newin;
            if (strenin == -1)
            {
              newin = strengthen(eallpositive, out, gram.root, funcvars);
              if (!newin)
              {
                assert(0 && "Can't handle non-positive NEWIN");
              }
              addInput(newin, gram.root, funcvars);
            }
            else
            {
              newin = strengthen(summ[strenin].first,out,gram.root,funcvars);
              assert(newin);
              summ[strenin].first = newin;
              summ_to_in[summ[strenin].second.get()] = newin;
            }
            backtrack = true;
          }
        if (!backtrack && refine_probs.size() != 0)
          assert(0 && "Refining summaries unimplemented");

        /*for (int j = 0; j < summ.size(); ++j)
        {
          if (summ[j].second->count(thiskey) == 0)
            continue;
          Expr out = summ[j].second->at(thiskey)[i];
          if (isUnreal(summ[j].first, out))
          { good = true; break; }
        }
        assert(good);*/

        if (backtrack)
        {
          if (params.debug)
            outs() << "  " << summ.size() << " input sets after backtracking";
          if (params.debug > 2)
          {
            outs() << ":";
            for (const auto& i_summ : summ)
              outs() << "\n    " << i_summ.first;
          }
          if (params.debug)
            outs() << endl;

          break; // TODO: Maybe should continue instead? When?
        }

        /*assert(0 && "Adding new inputs unimplemented");

        asserts[0] = etrue;
        asserts[2] = etrue;
        for (const auto &i_summ : summ)
        {
          checkdisjs[1] = mk<NEG>(i_summ.second->at(thiskey)[i]);
          asserts[1] = mk<FORALL>(gram.root->left(),mknary<OR>(checkdisjs));
          tribool res = u.isSat(asserts);
          if (!res)
          {
            assert(0 && "Checking possible solution unimplemented");
          }
          // TODO: What to do if indeterminate?
          //else if (indeterminate(res))
            //assert(0 && "PruneTrav can't handle unknowns");
        }*/
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

      if (params.debug)
        outs() << "Done with depth " << maxdepth << "\n";

      if (backtrack)
      {
        if (params.debug)
          outs() << "Backtracking to depth 0\n";
        maxdepth = -1;
      }
      if (params.debug)
        outs() << endl;
    }
  }
};

}

#endif
