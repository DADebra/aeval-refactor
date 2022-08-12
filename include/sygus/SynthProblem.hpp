#ifndef __SYNTHPROBLEM_HPP__
#define __SYNTHPROBLEM_HPP__

#include <string>
#include <utility>
#include "ufo/Expr.hpp"
#include "expr/SMTUtils.hpp"

#include "gram/AllHeaders.hpp"

namespace yy { class parser; }

namespace ufo
{
using namespace std;
using namespace expr;

enum class SynthFuncType { NONE, SYNTH, INV };

class SynthFunc
{
  public:
  SynthFuncType type;
  Expr decl;
  vector<Expr> vars; // V: FAPP
  bool hasgram = false;
  Grammar gram;
  bool hasanyconst = false; // Uses '(Constant *)'

  SynthFunc() {}
  SynthFunc(SynthFuncType t, Expr _decl, const vector<Expr>& _vars) :
    type(t), decl(_decl), vars(_vars) {}
  SynthFunc(SynthFuncType t, Expr _d, const vector<Expr>& _v, const Grammar& _g, bool _hasac) :
    type(t), decl(_d), vars(_v), gram(_g), hasgram(true), hasanyconst(_hasac) {}

  // Convert to (define-fun ...)
  string GetDefFun(Expr def, SMTUtils& u, bool newlines = false) const
  {
    ostringstream os;
    os << "(define-fun " << decl->first() << " (";
    for (int i = 0; i < vars.size(); ++i)
    {
      const Expr& var = vars[i];
      if (i != 0) os << " ";
      os << "(" << var->first() << " "; u.print(var->last(), os); os << ")";
    }
    os << ") "; u.print(decl->last(), os);
    if (newlines) os << "\n";
    os << "  ";
    u.print(def, os);
    if (newlines) os << "\n";
    os << ")";
    os.flush();
    return os.str();
  }
};

class SynthProblem
{
  friend yy::parser;
  private:
  bool analyzed = false;

  string _logic;
  vector<SynthFunc> _synthfuncs;
  vector<Expr> _vars;
  vector<Expr> _constraints;
  unordered_map<SynthFunc*,Expr> _singleapps;
  unordered_map<Expr, SynthFunc*> _declToFunc;
  unordered_set<SynthFunc*> _gramFuncs;

  public:
  const string& logic;
  vector<SynthFunc>& synthfuncs;
  const vector<Expr>& vars;
  const vector<Expr> constraints;
  // Funcs which are always called with same args, subset of synthfuncs
  // K: Func, V: FAPP (the single one)
  const unordered_map<const SynthFunc*,Expr>& singleapps;
  // K: FDECL, V: SynthFunc
  const unordered_map<Expr, const SynthFunc*>& declToFunc;
  // The set of SynthFunc's that have grammars
  const unordered_set<const SynthFunc*>& gramFuncs;

  private:
  void fillDeclToFunc()
  {
    for (auto& func : _synthfuncs)
      _declToFunc.emplace(func.decl, &func);
  }

  void findGramFuncs()
  {
    for (auto& func : _synthfuncs)
      if (func.hasgram)
        _gramFuncs.insert(&func);
  }

  void findSingleApps()
  {
    unordered_map<Expr,Expr> apps; // K: FDECL, V: FAPP
    // If found app != apps[fdecl], then not single app

    unordered_set<Expr> fapps;
    for (const Expr &con : constraints)
    {
      filter(con, [] (Expr e) {return isOpX<FAPP>(e);}, inserter(fapps, fapps.end()));
    }

    for (const Expr &fapp : fapps)
    {
      Expr decl = fapp->left();
      if (apps.count(decl) == 0)
        apps[decl] = fapp;
      else if (apps.at(decl) != fapp)
        apps[decl] = NULL;
    }

    for (auto &func : _synthfuncs)
      if (apps.count(func.decl) != 0 && apps.at(func.decl))
        _singleapps[&func] = apps.at(func.decl);
  }

  void extractConsts()
  {
    // We're not using 'filter' because it'll pull out the integers
    // *inside* of the BitVector constants.
    for (const Expr &cons : _constraints)
      extractConstsHelper(cons);
  }

  void extractConstsHelper(Expr num)
  {
    if (bind::isNum(num))
    {
      // TODO: Figure out which grammar to put the constants in
      for (SynthFunc *func : _gramFuncs)
        func->gram.addConst(num);
      Expr neg = NULL;
      if (isOpX<MPZ>(num))
      {
        // To help the C++ template deduction.
        mpz_class negmpz = -getTerm<mpz_class>(num);
        neg = mkTerm(negmpz, num->efac());
      }
      else if (isOpX<MPQ>(num))
      {
        mpq_class negmpq = -getTerm<mpq_class>(num);
        neg = mkTerm(negmpq, num->efac());
      }
      else if (is_bvnum(num))
      {
        mpz_class negmpz = -bv::toMpz(num);
        neg = bv::bvnum(negmpz, bv::width(num->right()), num->efac());
      }

      if (neg && num != neg)
      {
        for (SynthFunc *func : _gramFuncs)
          func->gram.addConst(neg);
      }
    }
    else if (!isOpX<FDECL>(num) || !bind::isLit(num))
    {
      for (int i = 0; i < num->arity(); ++i)
        extractConstsHelper(num->arg(i));
    }
  }

  void addStaticConsts()
  {
    ExprFactory &efac = _synthfuncs[0].decl->efac();

    for (SynthFunc *func : _gramFuncs)
    {
      // Have to handle BitVectors separately since we don't know which
      // widths to add constants for.
      for (const auto& kv : func->gram.consts)
      {
        if (isOpX<BVSORT>(kv.first))
        {
          unsigned width = bv::width(kv.first);
          for (int i : {-1, 0, 1})
            func->gram.addConst(bv::bvnum(mpz_class(i), width, efac));
        }
      }
      for (int i : {-1, 0, 1})
      {
        func->gram.addConst(mkTerm(mpz_class(i), efac));
        func->gram.addConst(mkTerm(mpq_class(i, 1), efac));
      }
    }
  }

  public:
  void Analyze()
  {
    if (analyzed)
      return;

    fillDeclToFunc();
    findGramFuncs();
    findSingleApps();
    if (_gramFuncs.size() != 0)
    {
      extractConsts();
      addStaticConsts();
    }

    analyzed = true;
  }

  SynthProblem() :
    logic(_logic), synthfuncs(_synthfuncs), constraints(_constraints),
    vars((decltype(vars))_vars),
    singleapps((decltype(singleapps))_singleapps),
    declToFunc((decltype(declToFunc))_declToFunc),
    gramFuncs((decltype(gramFuncs))_gramFuncs) {}

  SynthProblem(const SynthProblem& o) = delete;

  SynthProblem(SynthProblem&& o) :
    _logic(std::move(o._logic)), _synthfuncs(std::move(o._synthfuncs)),
    _constraints(std::move(o._constraints)),
    _vars(std::move(o._vars)),
    _singleapps(std::move(o._singleapps)),
    logic(_logic), synthfuncs(_synthfuncs), constraints(_constraints),
    vars((decltype(vars))_vars),
    singleapps((decltype(singleapps))_singleapps),
    declToFunc((decltype(declToFunc))_declToFunc),
    gramFuncs((decltype(gramFuncs))_gramFuncs) {}

  SynthProblem& operator=(const SynthProblem& o) = delete;

  SynthProblem& operator=(SynthProblem&& o)
  {
    this->~SynthProblem();
    new (this) SynthProblem(std::move(o));
    return *this;
  }
};

}

#endif
