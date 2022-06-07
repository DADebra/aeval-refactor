#ifndef GRAMMAR__H__
#define GRAMMAR__H__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

namespace ufo
{

class Grammar
{
  private:

  CFGUtils cfgutils;

  NT _root;
  unordered_set<NT> _nts;
  unordered_map<NT, vector<Expr>> _prods;
  vector<Constraint> _constraints;
  unordered_map<NT, unordered_map<Expr, mpq_class>> _priomap;

  // Key: Sort, Value: Variables
  VarMap _vars;
  ExprUSet _varsCache;

  ConstMap _consts;
  ExprUSet _constsCache;

  // Special variables which get a new instance each time they're used
  unordered_set<Expr> _uniqueVars;

  // K: NT, V: NTs transitively reachable from K
  unordered_map<NT,unordered_set<NT>> _graph;
  bool graphIsOld = true; // Does _graph need to be re-generated?

  // K: NT, V: (K': Prod, V': K' is recursive w.r.t. K)
  unordered_map<NT,unordered_map<Expr,bool>> _isRecCache;

  tribool _isInfinite = indeterminate;

  // Functions called when the grammar is modified.
  // TODO: Also tell listener what changed (which production, etc.)
  unordered_set<std::shared_ptr<ModListener>> modListeners;

  void notifyListeners(ModClass cl, ModType ty);

  void invalidateCachedProps(ModClass cl, ModType ty)
  {
    if (cl == ModClass::PROD)
    {
      graphIsOld = true;
      _isInfinite = indeterminate;
    }
  }

  // Will fill _graph and _isRecCache
  void generateGraph();
  void generateGraph(NT start); // Helper

  void calcIsInfinite();

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
  const decltype(_uniqueVars)& uniqueVars = _uniqueVars;

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

  // Special variables which get a new instance each time they're used.
  // These need to be registered so the traversal knows to expand them.
  Expr addUniqueVar(Expr sort);
  template <typename Sort>
  Expr addUniqueVar(ExprFactory& efac);

  bool delUniqueVar(Expr sort);
  template <typename Sort>
  bool delUniqueVar(ExprFactory& efac);
  unordered_set<Expr>::iterator delUniqueVar(
    unordered_set<Expr>::const_iterator itr);

  bool addModListener(std::shared_ptr<ModListener> listener);
  bool delModListener(std::shared_ptr<ModListener> listener);

  /*** UTILITIES ***/
  bool satsConstraints(const ParseTree& pt) const;

  inline bool isNt(Expr e) const { return isOpX<FAPP>(e) && _prods.count(e) != 0; }
  inline bool isVar(Expr e) const
  {
    return _varsCache.count(e) != 0;
  }
  inline bool isConst(Expr e) const
  {
    return _constsCache.count(e) != 0;
  }
  inline bool isUniqueVar(Expr e) const
  {
    return _uniqueVars.count(e) != 0;
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

  bool isInfinite()
  {
    if (indeterminate(_isInfinite))
      calcIsInfinite();
    return bool(_isInfinite);
  }

  /*** C-TORS, ETC. ***/
  Grammar() {}
  Grammar(const Grammar& g) :
    _root(g._root),_nts(g._nts),_prods(g._prods),
    _priomap(g._priomap),_vars(g._vars),_consts(g._consts),
    _varsCache(g._varsCache),_constsCache(g._constsCache),
    _uniqueVars(g._uniqueVars),
    root(_root),nts(_nts),prods(_prods),constraints(_constraints),
    vars(_vars),consts(_consts),priomap(_priomap),graph(_graph),
    uniqueVars(_uniqueVars)
  {
    for (const Constraint& c : g._constraints)
      _constraints.push_back(Constraint(c, this));
  }
  Grammar(Grammar&& g) :
    _root(std::move(g._root)),_nts(std::move(g._nts)),
    _prods(std::move(g._prods)), _priomap(std::move(g._priomap)),
    _vars(std::move(g._vars)),_consts(std::move(g._consts)),
    _varsCache(std::move(g._varsCache)),_constsCache(std::move(g._constsCache)),
    _uniqueVars(std::move(g._uniqueVars)),
    root(_root),nts(_nts),prods(_prods),constraints(_constraints),
    vars(_vars),consts(_consts),priomap(_priomap),graph(_graph),
    uniqueVars(_uniqueVars)
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

namespace std
{
template<>
struct hash<ufo::VarType>
{
    size_t operator()(const ufo::VarType& vt) const
    {
        return std::hash<long>()((long)vt);
    }
};
}

#endif
