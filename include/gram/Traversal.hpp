#ifndef TRAVERSAL__HPP__
#define TRAVERSAL__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

namespace ufo
{

struct uniqvarless
{
  bool operator()(const Expr& l, const Expr& r) const
  {
    assert(isOpX<FAPP>(l) && isOpX<FAPP>(r));
    const string& lstr = getTerm<string>(l->left()->left());
    const string& rstr = getTerm<string>(r->left()->left());
    assert(lstr == rstr);

    assert(l->arity() == 2 && r->arity() == 2);
    assert(isOpX<MPZ>(l->right()) && isOpX<MPZ>(r->right()));
    const mpz_class& lnum = getTerm<mpz_class>(l->right());
    const mpz_class& rnum = getTerm<mpz_class>(r->right());
    return lnum < rnum;
  }
};

typedef unordered_map<Expr,set<Expr,uniqvarless>> UniqVarMap;

typedef size_t Path;
const Path rootpath = std::hash<int>()(1), nullpath = 0;
enum PathClass { C = 1, Q = 2 };

// Extend the hash of the current path 'currhash' by position 'index'
//   and class (queue or child) 'class'.
// This number is used to uniquely identify where we are
//   in the recursive invocations of 'newtrav'.
// Now the grammar path (i.e. derivation), because I think that's more useful,
//   i.e. pclass == Q is ignored.
inline Path nextpath(Path currhash, PathClass pclass, unsigned index)
{
  if (pclass != Q)
  {
    hash_combine(currhash, pclass);
    hash_combine(currhash, index + 1);
  }

  return currhash;
}

struct TravContext
{
  // The context of the current position, with holes.
  // E.g. '(+ Start! Start!!)'
  Expr holeyCtx;
  // K: Hole (e.g. 'Start!'), V: <1st: NT (e.g. 'Start'), 2nd: Curr rec depth>
  unordered_map<Expr, std::pair<Expr, int>> holes;
  // For internal use (allocating new holes)
  // K: NT, V: max hole for that NT
  unordered_map<Expr, Expr> maxholes;
};

// Paramteter is post-replacement
typedef function<tribool(const Expr&,const TravContext&,const Expr&,const Expr&,int)> PrunePathFn;
tribool DefaultPrunePathFn(const Expr &prod, const TravContext& ctx, const Expr& hole, const Expr& nt, int currdepth)
{ return false; }

typedef function<PruneRetType(const Expr&,const vector<ParseTree>&,const TravContext&,const Expr&,const Expr&,int)> PruneArgFn;

class Traversal
{
  public:

  virtual ~Traversal() {}

  // Returns true if all candidates in the grammar have been enumerated.
  virtual bool IsDone() = 0;

  // Returns true if all candidates at the current recursion depth.
  // have been enumerated.
  virtual bool IsDepthDone() = 0;

  // Get the recursion depth currently used as maximum.
  virtual int GetCurrDepth() = 0;

  // Returns the candidate at the current traversal position
  // (with simplification applied if requested).
  virtual ParseTree GetCurrCand() = 0;

  // Returns the candidate at the current traversal position
  // (without simplification applied).
  virtual ParseTree GetUnsimplifiedCand() = 0;

  // Returns the set of unique variables that appear in the current candidate.
  // Key: Variable (added with 'Grammar::addUniqueVar')
  // Value: Set of unique FAPPS that Key expands to.
  virtual const UniqVarMap& GetCurrUniqueVars() = 0;

  // Increments the position of this traversal, returning the next candidate
  // (i.e. the candidate at the new position).
  virtual ParseTree Increment() = 0;

  // Must call when traversal is completed. `success` is true if the problem
  // was solved correctly. Mostly for debug printing, etc. purposes.
  virtual void Finish(bool success) = 0;
};

}
#endif
