#ifndef GRAMMAR__H__
#define GRAMMAR__H__

#include "gram/Constraint.h"

namespace ufo
{

typedef Expr NT;

enum class VarType { UNK, INC, DEC, CONST };

struct Var {
  VarType type;
  Expr expr;

  Var(Expr e) : expr(e), type(VarType::UNK) {}
  Var(Expr e, VarType ty) : expr(e), type(ty) {}

  operator Expr() const
  {
    return expr;
  }
};

struct varless
{
  bool operator()(const Var& l, const Var& r) const
  {
    string lstr = lexical_cast<string>(fname(l.expr)->left());
    string rstr = lexical_cast<string>(fname(r.expr)->left());
    return lstr < rstr;
  }
};

typedef unordered_map<Expr, set<Var, varless>> VarMap;
typedef unordered_map<Expr, vector<Expr>> ConstMap;

class Grammar
{
  //private:
  public:

  NT root;
  ExprUMap defs;
  vector<Constraint> constraints;
  unordered_map<std::pair<Expr,Expr>, cpp_rational> priomap;
  inline cpp_rational priomapat(const std::pair<Expr,Expr> &prod)
  {
    if (priomap.count(prod) == 0)
      priomap.emplace(prod, 1);
    return priomap[prod];
  }

  // priomap, but for getRandCand
  // Key: Either Expr, Value: Distribution, in order given by CFG
  unordered_map<Expr, discrete_distribution<int>> distmap;

  // Key: Sort, Value: Variables
  VarMap vars;

  ConstMap consts;

  public:
  
  Grammar() : root(NULL) {}

  // Add a non-terminal with the given name, sort, and productions.
  // 'prods' is an ordered vector of productions; the float is used to specify
  //   priorities with each production.
  template <typename Sort>
  NT addNt(string name, vector<pair<NT,float>> prods);

  // Add a non-terminal with the given name, sort, and productions.
  // 'prods' is an ordered vector of productions.
  template <typename Sort>
  NT addNt(string name, vector<NT> prods);

  void addConstraint(Expr constraint, bool any = false);

  template <typename Sort>
  void addConstants(ExprVector consts);

  void addVars(Expr sort, ExprVector vars);

  bool satsConstraints(const ParseTree& pt);

  friend class CFGUtils;
};

}

#endif
