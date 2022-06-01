#ifndef __GRAMMARTYPES_HPP__
#define __GRAMMARTYPES_HPP__

namespace ufo
{

typedef Expr NT;

enum class VarType { NONE, UNK, INC, DEC, CONST };

struct Var {
  VarType type;
  Expr expr;

  Var(Expr e) : expr(e), type(VarType::UNK) {}
  Var(Expr e, VarType ty) : expr(e), type(ty) { assert(ty != VarType::NONE); }

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

struct constless
{
  bool operator()(const Expr& l, const Expr& r) const
  {
    if (isOpX<MPQ>(l) && isOpX<MPQ>(r))
      return getTerm<mpq_class>(l) < getTerm<mpq_class>(r);
    else if (isOpX<MPZ>(l) && isOpX<MPZ>(r))
      return getTerm<mpz_class>(l) < getTerm<mpz_class>(r);
    else if (is_bvnum(l) && is_bvnum(r))
      return toMpz(l) < toMpz(r);
    else
      assert(0 && "Unknown constant type or non-matching types");
    return false;
  }
};

typedef unordered_map<Expr, set<Var, varless>> VarMap;
typedef unordered_map<Expr, set<Expr, constless>> ConstMap;

// Class of modification made to the grammar
enum class ModClass { NONE, PROD, CONSTRAINT, VAR, CONST, PRIO };
// Type of modification made
enum class ModType  { NONE, ADD, DEL, MOD };

typedef function<void(ModClass,ModType)> ModListener;

}

#endif
