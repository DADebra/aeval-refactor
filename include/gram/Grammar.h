#ifndef GRAMMAR__H__
#define GRAMMAR__H__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

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

class Grammar
{
  private:

  NT _root;
  set<NT> _nts;
  unordered_map<NT, vector<Expr>> _prods;
  vector<Constraint> _constraints;
  unordered_map<NT, unordered_map<Expr, mpq_class>> _priomap;

  // Key: Sort, Value: Variables
  VarMap _vars;

  ConstMap _consts;

  // K: NT, V: NTs transitively reachable from K
  unordered_map<NT,unordered_set<NT>> _graph;
  bool graphIsOld = true; // Does _graph need to be re-generated?
  void graphOnGramMod(ModClass cl, ModType ty)
  {
    if (cl == ModClass::PROD)
      graphIsOld = true;
  }

  // K: NT, V: (K': Prod, V': K' is recursive w.r.t. K)
  unordered_map<NT,unordered_map<Expr,bool>> _isRecCache;

  // Functions called when the grammar is modified.
  // TODO: Also tell listener what changed (which production, etc.)
  unordered_set<std::shared_ptr<ModListener>> modListeners;

  void notifyListeners(ModClass cl, ModType ty);

  // Will fill _graph and _isRecCache
  void generateGraph();
  void generateGraph(NT start); // Helper

  public:
  
  /*** GETTERS ***/

  const decltype(_root)& root = _root;
  const decltype(_nts)& nts = _nts;
  const decltype(_prods)& prods = _prods;
  const decltype(_constraints)& constraints = _constraints;
  const decltype(_priomap)& priomap = _priomap;
  const decltype(_vars)& vars = _vars;
  const decltype(_consts)& consts = _consts;
  const decltype(_graph)& graph = _graph;

  /*** MODIFIERS ***/

  void setRoot(NT root) { _root = root; }

  // Add a non-terminal with the given name and sort.
  template <typename Sort>
  NT addNt(string name, ExprFactory& efac);
  NT addNt(string name, Expr sort);
  NT addNt(Expr ntFapp);

  bool addProd(NT nt, Expr prod, mpq_class prio = 1);

  bool delProd(NT nt, Expr prod);
  vector<Expr>::iterator delProd(unordered_map<Expr,vector<Expr>>::iterator itr1,
    vector<Expr>::const_iterator itr2);

  void changePrio(NT nt, Expr prod, mpq_class prio);

  bool addConstraint(Expr cons, bool any = false);
  bool delConstraint(Expr cons);
  vector<Constraint>::iterator delConstraint(vector<Constraint>::const_iterator itr);

  // Add a constant
  bool addConst(Expr c, mpq_class prio = 1);
  bool delConst(Expr c);
  ConstMap::mapped_type::iterator delConst(ConstMap::iterator itr1,
    ConstMap::mapped_type::const_iterator itr2);

  bool addVar(Var var, mpq_class prio = 1);
  bool delVar(Var var);
  VarMap::mapped_type::iterator delVar(VarMap::iterator itr1,
    VarMap::mapped_type::const_iterator itr2);

  bool addModListener(std::shared_ptr<ModListener> listener);
  bool delModListener(std::shared_ptr<ModListener> listener);

  /*** UTILITIES ***/
  bool satsConstraints(const ParseTree& pt) const;

  inline bool isNt(Expr e) const { return isOpX<FAPP>(e) && _prods.count(e) != 0; }
  inline bool isVar(Expr e) const
  {
    return isOpX<FAPP>(e) &&
      _vars.count(typeOf(e)) != 0 && _vars.at(typeOf(e)).count(e) != 0;
  }
  inline bool isConst(Expr e) const
  {
    return bind::isLit(e) &&
      _consts.count(typeOf(e)) != 0 && _consts.at(typeOf(e)).count(e) != 0;
  }

  inline bool isRecursive(Expr prod, NT nt)
  {
    if (graphIsOld)
      generateGraph();
    return _isRecCache.at(nt).at(prod);
  }

  // Does path exist from nt1 to nt2 (nt2 is reachable from nt1)?
  inline bool pathExists(NT nt1, NT nt2)
  {
    if (graphIsOld)
      generateGraph();
    return _graph.at(nt1).count(nt2) != 0;
  }

  /*** C-TORS, ETC. ***/
  Grammar() {}
  Grammar(const Grammar& g) :
    _root(g._root),_nts(g._nts),_prods(g._prods),
    _priomap(g._priomap),_vars(g._vars),_consts(g._consts),
    root(_root),nts(_nts),prods(_prods),constraints(_constraints),
    vars(_vars),consts(_consts),priomap(_priomap),graph(_graph)
  {
    for (const Constraint& c : g._constraints)
      _constraints.push_back(Constraint(c, this));
  }
  Grammar(Grammar&& g) :
    _root(std::move(g._root)),_nts(std::move(g._nts)),
    _prods(std::move(g._prods)),
    _priomap(std::move(g._priomap)),
    _vars(std::move(g._vars)),_consts(std::move(g._consts)),
    root(_root),nts(_nts),prods(_prods),constraints(_constraints),
    vars(_vars),consts(_consts),priomap(_priomap),graph(_graph)
  {
    for (const Constraint& c : g._constraints)
      _constraints.push_back(Constraint(std::move(c), this));
    g._constraints.clear();
  }

  Grammar& operator=(const Grammar& g)
  { this->~Grammar(); new (this) Grammar(g); return *this; }
  Grammar& operator=(Grammar&& g)
  { this->~Grammar(); new (this) Grammar(std::move(g)); return *this; }

  friend class CFGUtils;
};

}

#endif
