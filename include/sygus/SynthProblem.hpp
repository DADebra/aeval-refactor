#ifndef __SYNTHPROBLEM_HPP__
#define __SYNTHPROBLEM_HPP__

#include <string>
#include "ufo/Expr.hpp"
#include "ae/SMTUtils.hpp"

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

  SynthFunc(SynthFuncType _type, Expr _decl, const vector<Expr>& _vars) :
    type(_type), decl(_decl), vars(_vars) {}
  SynthFunc(SynthFuncType _type, Expr _decl, vector<Expr>&& _vars) :
    type(_type), decl(_decl), vars(_vars) {}

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
  vector<Expr> _constraints;
  unordered_map<Expr,Expr> _singleapps;

  public:
  const string& logic;
  const vector<SynthFunc>& synthfuncs;
  const vector<Expr> constraints;
  // Funcs which are always called with same args, subset of synthfuncs
  // K: FDECL, V: FAPP (the single one)
  const unordered_map<Expr,Expr>& singleapps;

  private:
  void findSingleApps()
  {
    unordered_map<Expr,Expr> apps; // K: FDECL, V: FAPP
    // If found app != apps[fdecl], then not single app

    for (const auto &func : synthfuncs)
      _singleapps[func.decl] = NULL;

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
        _singleapps.erase(decl);
    }

    for (const auto &kv : _singleapps)
    {
      if (apps.count(kv.first) != 0)
      {
        _singleapps.at(kv.first) = apps.at(kv.first);
      }
    }
  }

  public:
  void Analyze()
  {
    if (analyzed)
      return;

    findSingleApps();

    analyzed = true;
  }

  SynthProblem() :
    logic(_logic), synthfuncs(_synthfuncs), constraints(_constraints),
    singleapps(_singleapps) {}

  SynthProblem(const SynthProblem& o) :
    _logic(o._logic), _synthfuncs(o._synthfuncs), _constraints(o._constraints),
    _singleapps(o._singleapps),
    logic(_logic), synthfuncs(_synthfuncs), constraints(_constraints),
    singleapps(_singleapps) {}

  SynthProblem(SynthProblem&& o) :
    _logic(std::move(o._logic)), _synthfuncs(std::move(o._synthfuncs)),
    _constraints(std::move(o._constraints)),
    _singleapps(std::move(o._singleapps)),
    logic(_logic), synthfuncs(_synthfuncs), constraints(_constraints), singleapps(_singleapps) {}

  SynthProblem& operator=(const SynthProblem& o)
  {
    this->~SynthProblem();
    new (this) SynthProblem(o);
    return *this;
  }

  SynthProblem& operator=(SynthProblem&& o)
  {
    this->~SynthProblem();
    new (this) SynthProblem(std::move(o));
    return *this;
  }
};

}

#endif
