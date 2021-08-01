#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"

#include <fstream>
#include <cctype>
#include <regex>
#include <tuple>

#include <boost/coroutine2/coroutine.hpp>
#include <boost/optional.hpp>
#include <boost/optional/optional_io.hpp>

using namespace std;
using namespace boost;
using namespace boost::coroutines2;

namespace ufo
{
  const char* ANY_INV = "ANY_INV";
  const char* INT_CONSTS = "INT_CONSTS";
  // The maximum number of previous candidates we store.
  const int MAXGRAMCANDS = 100;

  typedef unordered_set<Expr> ExprUSet;
  typedef unordered_map<Expr, Expr> ExprUMap;

  // Candidate generation method.
  //   RND - Completely random candidate without replacement.
  //   TRAV - Traverse full grammar up to specified depth.
  enum class GramGenMethod { RND, TRAV };

  enum class TravParamDirection { LTR, RTL, RND };
  enum class TravParamOrder { FORWARD, REVERSE, RND };
  enum class TravParamType { ORDERED, STRIPED };
  enum class TravParamPrio { SFS, DFS, BFS };

  // Parameters for generation using grammar.
  //   1st - GramGenMethod
  //   2nd - Maximum recursion depth
  typedef std::tuple<GramGenMethod, int, TravParamDirection, TravParamOrder,
          TravParamType, TravParamPrio> GramParams;

  class GRAMfactory
  {
    private:

    // A coroutine returning an Expr.
    typedef coroutine<Expr>::pull_type ExprCoro;

    class ExprCoroCacheIter;

    class ExprCoroCache
    {
      public:
      vector<Expr> outcache;
      ExprCoro coro;

      ExprCoroCache(ExprCoro _coro) : coro(std::move(_coro)) {}

      ExprCoroCacheIter begin()
      {
        return ExprCoroCacheIter(0, *this);
      }

      ExprCoroCacheIter end()
      {
        return ExprCoroCacheIter(-1, *this);
      }
    };

    class ExprCoroCacheIter
    {
      int pos = 0;
      ExprCoroCache &cache;

      inline void advancecoro()
      {
        while (cache.outcache.size() <= pos && cache.coro)
        {
          cache.outcache.push_back(cache.coro.get());
          cache.coro();
        }
        if (cache.outcache.size() <= pos)
          pos = -1;
      }

      public:

      ExprCoroCacheIter(int _pos, ExprCoroCache& _cache) : pos(_pos),
        cache(_cache) {}

      operator bool()
      {
        return pos >= 0;
      }

      Expr get()
      {
        if (pos < 0)
          return nullptr;

        advancecoro();

        if (pos < 0)
          return nullptr;

        return cache.outcache[pos];
      }

      void operator()()
      {
        ++pos;
        advancecoro();
      }

      ExprCoroCacheIter& operator++()
      {
        ++pos;
        advancecoro();
        return *this;
      }

      Expr operator*()
      {
        return get();
      }

      ExprCoroCacheIter begin()
      {
        return std::move(ExprCoroCacheIter(pos, cache));
      }

      ExprCoroCacheIter end()
      {
        return std::move(ExprCoroCacheIter(-1, cache));
      }
    };

    class tuplehash
    {
      public:
      size_t operator()(const std::tuple<Expr,int,std::shared_ptr<ExprUSet>,
      Expr>& tup) const
      {
        return std::hash<Expr>()(std::get<0>(tup)) *
          std::hash<int>()(std::get<1>(tup)) *
          std::hash<std::shared_ptr<ExprUSet>>()(std::get<2>(tup)) *
          std::hash<Expr>()(std::get<3>(tup));
      }
    };

    class pairhash
    {
      public:
      size_t operator()(const std::pair<Expr,Expr>& pr) const
      {
        return std::hash<Expr>()(pr.first) * std::hash<Expr>()(pr.second);
      }
    };

    // The main coroutine we use to traverse the grammar.
    std::unique_ptr<ExprCoro> getNextCandTrav;

    // Needed for candidate generation.
    ExprFactory &m_efac;

    // Needed for parsing grammar.
    EZ3 &z3;

    // Previously generated candidates from sample grammar
    ExprUSet gramCands;
    deque<Expr> gramCandsOrder;

    // Variables for debugging coroutine creation/deletion
    //unordered_map<Expr, int> currnumtravcoros;
    //int currnumcandcoros = 0;

    // The sub-candidates previously generated with root == key
    unordered_map<std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr>,
      ExprCoroCache,tuplehash> corocache;

    // Key: Non-terminal, Value: Productions in b/ieither# format
    ExprUMap defs;

    // Key: <Non-terminal, Production>, Value: Priority
    unordered_map<std::pair<Expr, Expr>, cpp_rational, pairhash> priomap;

    // The root of the tree of the grammar
    Expr inv;

    // All variables mentioned in the file, regardless of type.
    // Variables are for the invariant stored in 'inv'
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprUSet> inv_vars;

    // Variables for the other invariants in the input file.
    // Key: Sort, Value: List of variables of that sort.
    unordered_map<Expr, ExprUSet> other_inv_vars;

    // Set of integer constants that appear in the program.
    ExprUSet int_consts;

    // Whether to print debugging information or not.
    bool printLog;

    /*** PARAMETERS (respective to GramParams) ***/

    // How this GRAMfactory will generate candidates.
    GramGenMethod genmethod;

    // The maximum recursion depth during traversal.
    int maxrecdepth;

    TravParamDirection travdir;
    TravParamOrder travorder;
    TravParamType travtype;
    TravParamPrio travprio;

    public:

    bool initialized = false;

    private:

    // exp is e.g. (= iterm iterm), nonterm is e.g. iterm
    bool isRecursive(Expr exp, Expr nonterm)
    {
      for (auto itr = exp->args_begin(); itr != exp->args_end(); ++itr)
      {
        if (isRecursive(*itr, nonterm))
          return true;
      }
      // Handle simple recursion
      if (exp == nonterm)
        return true;

      return false;
    }

    void getNextCandTrav_fn(coroutine<Expr>::push_type &sink,
        Expr root = NULL, int currdepth = 0,
        std::shared_ptr<ExprUSet> qvars = NULL, Expr currnt = NULL)
    {
      //currnumcandcoros++;
      if (root == NULL)
        root = inv;

      /*outs() << "getNextCandTrav(" << root << ", " << currdepth << ", ";
      if (qvars != NULL)
        printvec(outs(), *qvars);
      else
        outs() << "NULL";
      outs() << ", " << currnt << ")" << endl;*/

      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const ExprUSet &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          sink(root);
          //currnumcandcoros--;
          return;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname.find("either") != string::npos)
        {
          vector<int> order;

          if (travorder == TravParamOrder::FORWARD)
            for (int i = 1; i < root->arity(); ++i)
            {
              if (!isRecursive(root->arg(i), currnt) ||
              currdepth + 1 <= maxrecdepth)
                order.push_back(i);
            }
          else if (travorder == TravParamOrder::REVERSE)
            for (int i = root->arity() - 1; i >= 1; --i)
            {
              if (!isRecursive(root->arg(i), currnt) ||
              currdepth + 1 <= maxrecdepth)
                order.push_back(i);
            }
          else if (travorder == TravParamOrder::RND)
          {
            set<int> done;
            while (done.size() < root->arity() - 1)
            {
              // Offset by 1 because arg(0) is the fdecl.
              int randnum = (rand() % (root->arity() - 1)) + 1;

              if (!done.insert(randnum).second)
                continue;

              // Don't traverse past maximum depth
              if (!isRecursive(root->arg(randnum), currnt) ||
              currdepth + 1 <= maxrecdepth)
                order.push_back(randnum);
            }
          }

          if (order.size() == 0)
          {
            sink(NULL);
            return;
          }

          // First: Production, Second: Coroutine
          list<std::pair<std::pair<Expr,Expr>,ExprCoroCacheIter>> coros;
          for (int i : order)
          {
            int newdepth;
            if (isRecursive(root->arg(i), currnt))
              newdepth = currdepth + 1;
            else
              newdepth = currdepth;

            coros.push_back(std::move(make_pair(make_pair(root->arg(i),
              currnt), getCandCoro(root->arg(i), newdepth, qvars,currnt))));
            if (*coros.back().second == NULL)
              coros.pop_back();
            else if (travtype == TravParamType::STRIPED)
            {
              sink(*coros.back().second);
              ++coros.back().second;
              if (!coros.back().second)
                coros.pop_back();
            }
          }

          auto lastbest = coros.begin();

          // Key: <Production, Non-terminal>,
          // Value: number of cands generated with Production
          unordered_map<std::pair<Expr, Expr>, int, pairhash> candnum;
          int totalcandnum = 0;


          // prod has same format as Key of candnum
          auto shoulddefer = [&] (const std::pair<Expr,Expr>& prod) -> bool
          {
            if (candnum[prod] == 0 || priomap[prod] == 1)
              return false;
            return candnum[prod] > (int)(priomap[prod]*totalcandnum);
          };

          for (auto &kv : coros)
          {
            candnum[kv.first] = 0;
          }

          while (coros.size() != 0)
          {
            bool didsink = false;

            if (travtype == TravParamType::ORDERED)
            {
              auto itr = coros.begin();
              if (coros.size() != 0 && itr != coros.end())
              {
                while (itr != coros.end() && shoulddefer(itr->first))
                  ++itr;

                if (itr != coros.end())
                {
                  sink(*itr->second);
                  candnum[itr->first]++;
                  ++itr->second;
                  if (!itr->second)
                  {
                    itr = coros.erase(itr);
                    lastbest = coros.begin();
                  }
                  didsink = true;
                }
              }
            }
            else if (travtype == TravParamType::STRIPED)
            {
              for (auto itr = coros.begin(); itr != coros.end();)
              {
                if (shoulddefer(itr->first))
                {
                  ++itr;
                  continue;
                }

                sink(*itr->second);
                didsink = true;
                candnum[itr->first]++;
                ++itr->second;
                if (!itr->second)
                {
                  auto olditr = itr;
                  itr = coros.erase(itr);
                  if (lastbest == olditr)
                    lastbest = coros.begin();
                  continue;
                }
                ++itr;
              }
            }

            if (coros.size() != 0 && !didsink)
            {
              // No coroutines available, pick best option.
              if (!lastbest->second)
                lastbest = coros.begin();
              auto bestcoro = lastbest;
              bool setbestcoro = false;
              for (auto itr = coros.begin(); itr != lastbest; ++itr)
              {
                if (priomap[itr->first] > priomap[bestcoro->first])
                {
                  bestcoro = itr;
                  setbestcoro = true;
                }
              }

              if (!setbestcoro)
              {
                auto itr = lastbest;
                if (travtype == TravParamType::STRIPED)
                  ++itr;
                for (; itr != coros.end(); ++itr)
                {
                  if (priomap[itr->first] >= priomap[bestcoro->first])
                  {
                    bestcoro = itr;
                    setbestcoro = true;
                    break;
                  }
                }
              }

              sink(*bestcoro->second);
              candnum[bestcoro->first]++;
              ++bestcoro->second;
              if (!bestcoro->second)
              {
                auto oldbestcoro = bestcoro;
                bestcoro = coros.erase(bestcoro);
                if (lastbest == oldbestcoro)
                  lastbest = coros.begin();
                continue;
              }
            }
          }

          //currnumcandcoros--;
          return;
        }
        else
        {
          // Root is user-defined non-terminal
          if (defs[root] != NULL)
          {
            //currnumcandcoros--;
            return getNextCandTrav_fn(sink, defs[root], root == currnt ?
              currdepth : 0, qvars, root);
          }
          else if (qvars != NULL &&
          qvars->find(root->first()) != qvars->end())
          {
              // Root is a variable for a surrounding quantifier
              sink(root);
              //currnumcandcoros--;
              return;
          }
          else
          {
            // There's no definition, we're expanding an empty *_VARS
            outs() << "ERROR: There is no definition for user-defined " <<
              "non-terminal " << root << " in the CFG for " << inv <<
              ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
            exit(1);
          }
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        sink(root);
        //currnumcandcoros--;
        return;
      }

      // Root is Z3-defined non-terminal

      std::shared_ptr<ExprUSet> localqvars(new ExprUSet());

      if (qvars != NULL)
        for (auto& var : *qvars)
          localqvars->insert(var);

      if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      {
        // Add quantifier variables to qvars
        for (int i = 0; i < root->arity() - 1; ++i)
        {
          localqvars->insert(root->arg(i));
        }
      }

      // The set of Expr's we'll use to generate this n-ary expression.
      ExprVector expanded_args;
      // The corresponding coroutines for each entry in expanded_args.
      vector<optional<ExprCoroCacheIter>> argcoros;

      // Initialize all arguments to valid Expr's;
      //   otherwise we can't do mkNary below.
      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
      {
        if (travtype == TravParamType::ORDERED)
        {
          argcoros.push_back(boost::none);
          expanded_args.push_back(NULL);
        }
        else
        {
          argcoros.push_back(getCandCoro(*itr,currdepth,localqvars,currnt));
          expanded_args.push_back(argcoros.back()->get());
          (*argcoros.back())();
        }
      }

      ExprCoro thistrav = getTravCoro(std::move(argcoros),
        std::move(expanded_args), std::move(set<int>()), root, currdepth,
        localqvars, currnt);

      for (Expr exp : thistrav)
      {
        sink(exp);
      }

      // Traversal of root done.
      //currnumcandcoros--;
      return;
    }
    ExprCoroCacheIter getCandCoro(Expr root = NULL, int currdepth = 0,
      std::shared_ptr<ExprUSet> qvars = NULL, Expr currnt = NULL)
    {
      std::tuple<Expr,int,std::shared_ptr<ExprUSet>,Expr> tup =
        make_tuple(root, currdepth, qvars, currnt);
      bool didemplace = false;
      if (corocache.find(tup) == corocache.end())
      {
        corocache.emplace(tup, std::move(ExprCoroCache(std::move(
          ExprCoro(std::bind(&GRAMfactory::getNextCandTrav_fn, this,
          std::placeholders::_1, root, currdepth, qvars, currnt))))));
        didemplace = true;
      }
      return corocache.at(tup).begin();
    }

    template<typename T>
    void printvec(std::ostream &os, T vec)
    {
      os << "[";
      for (auto &t : vec)
      {
        os << " " << t;
      }
      os << " ]";
    }

    void travCand_fn(coroutine<Expr>::push_type& sink,
        vector<optional<ExprCoroCacheIter>> coros, ExprVector cand,
        set<int> stuck, Expr root, int currdepth,
        std::shared_ptr<ExprUSet> qvars, Expr currnt)
    {
      //currnumtravcoros[root]++;
      /*outs() << "travCand_fn([";
      for (auto &opt : coros)
      {
        if (opt)
          outs() << " " << &*opt;
        else
          outs() << " none";
      }
      outs() << " ], ";
      printvec(outs(), cand);
      outs() << ", ";
      printvec(outs(), stuck);
      outs() << ")" << endl;*/
      if (travtype == TravParamType::STRIPED ||
      stuck.size() == cand.size())
        sink(m_efac.mkNary(root->op(), cand));

      if (stuck.size() == cand.size())
        return;

      vector<ExprCoro> methcoros;
      auto emptymethcoros = [&] () {
        bool methcoroavail = true;
        while (methcoroavail)
        {
          methcoroavail = false;
          for (auto& meth : methcoros)
          {
            if (meth)
            {
              sink(meth.get());
              meth();
              methcoroavail = true;
            }
          }
        }
        methcoros.clear();
      };

      if (travtype == TravParamType::STRIPED)
      {
        vector<int> free;
        int min_i = 0, max_i = coros.size();
        if (stuck.size() != 0)
          min_i = *(--stuck.end()) + 1;
        if (travdir == TravParamDirection::LTR)
          for (int i = min_i; i < max_i; ++i)
            free.push_back(i);
        else if (travdir == TravParamDirection::RTL)
          for (int i = max_i - 1; i >= min_i; --i)
            free.push_back(i);

        if (travdir == TravParamDirection::RND)
          random_shuffle(free.begin(), free.end());

        auto inloopfn = [&] (int pos) -> bool {
          if (!*coros[pos])
            return false;

          ExprVector newcand = cand;
          newcand[pos] = coros[pos]->get();
          (*coros[pos])();
          set<int> newstuck = stuck;
          for (int i = 0; i <= pos; ++i)
            newstuck.insert(i);

          if (newstuck.size() == newcand.size())
            sink(m_efac.mkNary(root->op(), newcand));
          else
          {
            vector<optional<ExprCoroCacheIter>> newcoros;
            for (int i = 0; i < coros.size(); ++i)
            {
              if (newstuck.find(i) == newstuck.end())
              {
                newcoros.push_back(getCandCoro(root->arg(i), currdepth,
                    qvars, currnt));
                newcand[i] = newcoros[i]->get();
                (*newcoros[i])();
              }
              else
                newcoros.push_back(boost::none);
            }

            methcoros.push_back(getTravCoro(std::move(newcoros),
              std::move(newcand), std::move(newstuck), root, currdepth, qvars,
              currnt));
            sink(methcoros.back().get());
            methcoros.back()();
          }

          return true;
        };

        if (travprio != TravParamPrio::DFS)
        {
          bool coroavail = true;
          while (coroavail)
          {
            coroavail = false;
            for (int i : free)
              coroavail |= inloopfn(i);
            if (travprio == TravParamPrio::BFS)
              emptymethcoros();
          }
        }
        else
        {
          for (int i : free)
          {
            bool coroavail = true;
            while (coroavail)
              coroavail = inloopfn(i);
          }
        }
      }
      else if (travtype == TravParamType::ORDERED)
      {
        vector<int> free;
        for (int i = 0; i < cand.size(); ++i)
          if (stuck.find(i) == stuck.end())
            free.push_back(i);

        int nextstuck;
        if (travdir == TravParamDirection::LTR)
          nextstuck = free.back();
        else if (travdir == TravParamDirection::RTL)
          nextstuck = free.front();
        else if (travdir == TravParamDirection::RND)
          nextstuck = free[rand() % free.size()];

        ExprCoroCacheIter nextcoro = getCandCoro(root->arg(nextstuck),
          currdepth, qvars, currnt);

        set<int> newstuck = stuck;
        newstuck.insert(nextstuck);

        for (Expr exp : nextcoro)
        {
          cand[nextstuck] = exp;
          vector<optional<ExprCoroCacheIter>> newcoros;
          for (int i = 0; i < coros.size(); ++i)
            newcoros.push_back(boost::none);

          if (newstuck.size() == cand.size())
            sink(m_efac.mkNary(root->op(), cand));
          else
          {
            ExprCoro newmeth = getTravCoro(std::move(newcoros), cand,
              newstuck, root, currdepth, qvars, currnt);
            for (Expr exp : newmeth)
              sink(exp);
          }
        }
      }

      emptymethcoros();
      //currnumtravcoros[root]--;
    }

    ExprCoro getTravCoro(vector<optional<ExprCoroCacheIter>> coros,
      ExprVector cand, set<int> stuck, Expr root, int currdepth,
      std::shared_ptr<ExprUSet> qvars, Expr currnt)
    {
      // We can't use std::bind, since that will try to copy coros
      return std::move(ExprCoro([&] (coroutine<Expr>::push_type &sink) {
        return travCand_fn(sink, std::move(coros), std::move(cand),
          std::move(stuck), root, currdepth, qvars, currnt); }));
    }

    // qvars is set of quantifier variables for this expression.
    // Using pointer because we need it to be nullable.
    Expr getRandCand(Expr root, ExprUSet *qvars = NULL)
    {
      if (isOpX<FAPP>(root))
      {
        string fname = lexical_cast<string>(bind::fname(root)->left());
        const ExprUSet &sortvars = inv_vars[bind::typeOf(root)];
        if (sortvars.find(root) != sortvars.end())
        {
          // Root is a symbolic variable; don't expand.
          return root;
        }

        // Else, root is a user-defined non-terminal or *either*

        if (fname.find("either") != string::npos)
        {
          Expr cand = NULL;
          while (cand == NULL)
          {
            // Randomly select from the available productions.
            // Offset by 1 because arg(0) is the fdecl.
            int randindex = (rand() % (root->arity() - 1)) + 1;

            cand = getRandCand(root->arg(randindex), qvars);
            return cand;
          }
        }
        else
        {
          // Root is user-defined non-terminal
          if (defs[root] != NULL)
            return getRandCand(defs[root], qvars);
          else if (qvars != NULL &&
           qvars->find(root->first()) != qvars->end())
            // Root is a variable for a surrounding quantifier
            return root;
          else
          {
            // There's no definition, we're expanding an empty *_VARS
            outs() << "ERROR: There is no definition for user-defined " <<
              "non-terminal " << root << " in the CFG for " << inv <<
              ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
            exit(1);
            // We never get here
            return NULL;
          }
        }
      }
      else if (root->arity() == 0)
      {
        // Root is a Z3 terminal, e.g. Int constant, e.g. 3
        return root;
      }

      // Root is Z3-defined non-terminal

      ExprVector expanded_args;
      ExprUSet localqvars;

      if (qvars != NULL)
        for (auto& var : *qvars)
          localqvars.insert(var);

      if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
      {
        // Add quantifier variables to qvars
        for (int i = 0; i < root->arity() - 1; ++i)
        {
          localqvars.insert(root->arg(i));
        }
      }

      for (auto itr = root->args_begin();
           itr != root->args_end(); ++itr)
        expanded_args.push_back(getRandCand(*itr, &localqvars));

      // Don't generate undefined candidates (e.g. mod by 0)
      if (isOpX<MOD>(root) || isOpX<DIV>(root) || isOpX<IDIV>(root))
      {
        while (isOpX<MPZ>(expanded_args.back()) && lexical_cast<cpp_int>(expanded_args.back()) <= 0)
          expanded_args.back() = getRandCand(root->last(), qvars);
      }

      return m_efac.mkNary(root->op(), expanded_args);
    }

    public:

    GRAMfactory(ExprFactory &_efac, EZ3 &_z3, bool _printLog) :
      m_efac(_efac), z3(_z3), printLog(_printLog), inv(NULL),
      getNextCandTrav(nullptr) {}

    void addVar(Expr var)
    {
      inv_vars[bind::typeOf(var)].insert(var);
    }

    void addOtherVar(Expr var)
    {
      other_inv_vars[bind::typeOf(var)].insert(var);
    }

    void addIntConst(cpp_int iconst)
    {
      int_consts.insert(mkMPZ(iconst, m_efac));
    }

    void setParams(GramParams params)
    {
      std::tie(genmethod, maxrecdepth, travdir, travorder, travtype,
          travprio) = params;
    }

    GramParams getParams()
    {
      return std::move(std::make_tuple(genmethod, maxrecdepth, travdir,
            travorder, travtype, travprio));
    }

    // Parse the grammar file. Must be called after addVar(s).
    void initialize(string gram_file, string inv_fname)
    {
      // gram_file will be empty if we don't pass `--grammar` option
      if (!gram_file.empty())
      {
        // Read in entire user grammar
        ostringstream user_cfg;
        ifstream infile(gram_file);
        user_cfg << infile.rdbuf();

        // The set of eithers we need to generate.
        // Not worth making a distinction between sorts.
        unordered_set<int> eithers_to_gen;

        // Generate enough eithers for *_VARS
        for (auto& pair : inv_vars)
        {
          eithers_to_gen.insert(pair.second.size());
        }

        // Generate the eithers the user CFG uses.
        smatch eithermatch;
        regex eitherregex("either_([0-9]+)");
        string searchstr = user_cfg.str();

        while (regex_search(searchstr, eithermatch, eitherregex))
        {
          eithers_to_gen.insert(stoi(eithermatch[1]));
          searchstr = eithermatch.suffix().str();
        }

        // The provided grammar, plus variable definitions and special
        //   variables that we define.
        ostringstream aug_gram;

        auto generate_either_decl = [&] (string sort_name, string sort_smt)
        {
            // Generate either functions for given sort
            for (auto& i : eithers_to_gen)
            {
              aug_gram << "(declare-fun " << sort_name << "_either_" << i << " (";
              for (int x = 1; x <= i; ++x)
              {
                aug_gram << sort_smt << " ";
              }
              aug_gram << ") " << sort_smt << ")\n";
            }
        };

        // We need the Bool eithers for the inv definition (rel is Bool)
        aug_gram << "(declare-fun BOOL_VARS () Bool)" << endl;
        generate_either_decl("Bool", "Bool");
        aug_gram << "(declare-fun Bool_prio (Bool Real) Bool)\n";

        // Which sorts we've already generated eithers and *_VARS for.
        ExprSet donesorts;
        donesorts.insert(mk<BOOL_TY>(m_efac));

        // Easiest way to handle all_inv_vars and inv_vars
        auto generate_all = [&] (unordered_map<Expr, ExprUSet> vars,
            bool thisinv)
        {
          for (auto& pair : vars)
          {
            string sort_smt = z3_to_smtlib<EZ3>(z3, pair.first);

            string sort_name(sort_smt);

            if (sort_name.find("(") != string::npos)
            {
              // We have a parameterized sort (e.g. Array)
              for (auto&c : sort_name)
              {
                if (c == '(' || c == ')')
                  c = '$';
                else if (c == ' ')
                  c = '_';
              }
            }

            // Generate special variable for this sort
            string vars_name(sort_name);
              vars_name += "_VARS";
            for (auto& c : vars_name)
              c = (char)toupper(c);

            // If we haven't already generated an either
            if (donesorts.find(pair.first) == donesorts.end())
            {
              aug_gram << "(declare-fun " << vars_name << " () " << sort_smt << ")\n";

              generate_either_decl(sort_name, sort_smt);
              // Generate *_prio declarations
              aug_gram << "(declare-fun " << sort_name << "_prio (" << sort_smt << " Real) " << sort_smt << ")\n";
              donesorts.insert(pair.first);
            }

            // Generate _FH_* decls for this sort
            for (auto& var : pair.second)
            {
              // var is a FAPP
              aug_gram << z3_to_smtlib(z3, bind::fname(var)) << endl;
            }

            // Only generate definitions for variables of this SamplFactory's invariant
            if (thisinv)
            {
              // Generate definition (i.e. productions) for this sort's *_VARS
              if (pair.second.size() >= 1)
              {
                aug_gram << "(assert (= " << vars_name <<
                  " (" << sort_name << "_either_" << pair.second.size();

                for (auto& var : pair.second)
                {
                  aug_gram << " " << var;
                }

                aug_gram << ")))" << endl;
              }
              else if (pair.second.size() == 1)
              {
                aug_gram << "(assert (= " << vars_name << " " << *pair.second.begin() <<
                  "))" << endl;
              }
            }
          }
        };

        generate_all(inv_vars, true);
        generate_all(other_inv_vars, false);

        // Generate INT_CONSTS declaration
        aug_gram << "(declare-fun " << INT_CONSTS << " () Int)" << endl;

        aug_gram << user_cfg.str();

        if (printLog)
        {
          outs() << ";Provided user grammar: " << endl;
          outs() << aug_gram.str() << endl << endl;
        }

        // Parse combined grammar
        Expr gram = z3_from_smtlib<EZ3>(z3, aug_gram.str());

        // Find root of grammar and fill in `defs` map.
        for (auto iter = gram->args_begin(); iter != gram->args_end(); ++iter)
        {
          //ex is an assertion
          Expr ex = *iter;
          if (isOpX<EQ>(ex))
          {
            string ex_fname = lexical_cast<string>(bind::fname(ex->left())->left());
            if (ex_fname == ANY_INV && inv == NULL)
            {
              // Only use ANY_INV if we don't already have a specific one
              inv = ex->left();
            }
            else if (ex_fname == inv_fname)
            {
              inv = ex->left();
            }

            if (isOpX<FAPP>(ex->right()) &&
                lexical_cast<string>(bind::fname(ex->right())->left())
                .find("either") != string::npos)
            {
              ExprVector newdefargs;
              for (auto itr = ++ex->right()->args_begin();
                   itr != ex->right()->args_end(); ++itr)
              {
                if (isOpX<FAPP>(*itr) &&
                    lexical_cast<string>(bind::fname(*itr)->left())
                    .find("prio") != string::npos)
                {
                  std::pair<Expr,Expr> keypair((*itr)->arg(1), ex->left());
                  priomap[keypair] =
                    lexical_cast<cpp_rational>((*itr)->arg(2));
                  newdefargs.push_back((*itr)->arg(1));
                }
                else
                {
                  std::pair<Expr, Expr> keypair(*itr, ex->left());
                  priomap[keypair] = 1;
                  newdefargs.push_back(*itr);
                }
              }

              defs[ex->left()] = bind::fapp(ex->right()->left(), newdefargs);
            }
            else
              defs[ex->left()] = ex->right();
          }
        }
      }

      initialized = (inv != NULL);

      if (printLog)
      {
        if (initialized)
          outs() << "Using user-provided grammar(s)." << endl;
        else
          outs() << "Using built-in grammar." << endl;
      }
    }

    // Properly initialize INT_CONSTS now that we've found them
    void initialize_intconsts()
    {
      if (int_consts.size() != 0)
      {
        Expr eitherfunc = bind::fdecl(mkTerm(string("Int_either_") + to_string(int_consts.size()), m_efac),
            ExprVector(int_consts.size(), m_efac.mkTerm(INT_TY())));

        Expr int_consts_decl = bind::intConst(mkTerm(string(INT_CONSTS), m_efac));
        defs[int_consts_decl] = bind::fapp(eitherfunc, int_consts);
      }

      if (initialized && genmethod == GramGenMethod::TRAV)
      {
        std::shared_ptr<ExprUSet> qvars = NULL;
        int currdepth = 0;
        Expr currnt = NULL;
        getNextCandTrav = std::unique_ptr<ExprCoro>(new ExprCoro(
            std::bind(&GRAMfactory::getNextCandTrav_fn, this,
            std::placeholders::_1, inv, currdepth, qvars, currnt)));
      }
    }

    Expr getFreshCandidate()
    {
      if (inv == NULL)
        return NULL; // Should never happen, but handle just in case

      Expr nextcand = NULL;

      /*for (auto& kv : currnumtravcoros)
        outs() << "currnumtravcoros[" << kv.first << "] = " << kv.second << "\n";
      outs() << "currnumcandcoros = " << currnumcandcoros << "\n";*/

      // Generate a new candidate from the grammar, and simplify
      while (!nextcand)
      {
        if (genmethod == GramGenMethod::TRAV)
        {
          if (!*getNextCandTrav)
          {
            outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
            exit(0);
            return NULL;
          }
          nextcand = getNextCandTrav->get();
          (*getNextCandTrav)();
        }
        else if (genmethod == GramGenMethod::RND)
        {
          nextcand = getRandCand(inv);
        }
        //outs() << "Before simplification: " << nextcand << endl;
        nextcand = simplifyBool(simplifyArithm(nextcand));
        if (isOpX<TRUE>(nextcand) || isOpX<FALSE>(nextcand))
        {
          nextcand = NULL;
          //outs() << "Tautology/Contradiction" << endl;
        }
        else if (!gramCands.insert(nextcand).second)
        {
          nextcand = NULL;
          //outs() << "Old candidate" << endl;
        }
        else
        {
          if (gramCandsOrder.size() == MAXGRAMCANDS)
          {
            gramCands.erase(gramCandsOrder[0]);
            gramCandsOrder.pop_front();
          }
          gramCandsOrder.push_back(nextcand);
          break;
        }
      }

      return nextcand;
    }
  };

  class CFGUtils
  {
    public:

    // Returns the path to the CFG (within 'grams') corresponding to invDecl.
    // Returns the empty string if no appropriate CFG is found.
    // Set 'useany' to only look for ANY_INV.
    static string findGram(vector<string>& grams, Expr invDecl,
        bool useany = false)
    {
      string invName = lexical_cast<string>(invDecl->left());

      // The declarations in the grammar we're looking for.
      // Note: a (declare-rel) won't work, so we don't need to look for it.
      string finddecl1 = "(declare-fun " + invName + " () Bool)";
      string finddecl2 = "(declare-var " + invName + " Bool)";
      string finddecl3 = string("(declare-fun ") + ANY_INV + " () Bool)";
      string finddecl4 = string("(declare-var ") + ANY_INV + " Bool)";

      for (auto& gramstr : grams)
      {
        ifstream gramfile(gramstr);
        string line;
        while (getline(gramfile, line))
        {
          if (!useany)
          {
            // Prioritize the exact invariant decl over ANY_INV
            if (line.find(finddecl1) != string::npos ||
              line.find(finddecl2) != string::npos)
            {
              gramfile.close();
              return gramstr;
            }
          }
          else
          {
            if (line.find(finddecl3) != string::npos ||
              line.find(finddecl4) != string::npos)
            {
              gramfile.close();
              return gramstr;
            }
          }
        }
      }

      if (!useany)
      {
        // Retry, looking for ANY_INV this time.
        return std::move(findGram(grams, invDecl, true));
      }
      else
      {
        // We've exhausted the list of grammars, return failure.
        return "";
      }
    }

    static GramGenMethod strtogenmethod(const char* methodstr)
    {
      if (!strcmp(methodstr, "rnd"))
        return GramGenMethod::RND;
      if (!strcmp(methodstr, "traverse"))
        return GramGenMethod::TRAV;

      outs() << "Error: Unrecognized --gen_method \"" << methodstr << "\"" << endl;
      exit(1);
      return GramGenMethod::RND;
    }
    static TravParamDirection strtotravdir(const char* str)
    {
      if (!strcmp(str, "ltr"))
        return TravParamDirection::LTR;
      if (!strcmp(str, "rtl"))
        return TravParamDirection::RTL;
      if (!strcmp(str, "rnd"))
        return TravParamDirection::RND;

      outs() << "Error: Unrecognized --trav_direction \"" << str << "\"" << endl;
      exit(1);
      return TravParamDirection::LTR;
    }
    static TravParamOrder strtotravord(const char* str)
    {
      if (!strcmp(str, "forward"))
        return TravParamOrder::FORWARD;
      if (!strcmp(str, "reverse"))
        return TravParamOrder::REVERSE;
      if (!strcmp(str, "rnd"))
        return TravParamOrder::RND;

      outs() << "Error: Unrecognized --trav_order \"" << str << "\"" << endl;
      exit(1);
      return TravParamOrder::FORWARD;
    }
    static TravParamType strtotravtype(const char* str)
    {
      if (!strcmp(str, "ordered"))
        return TravParamType::ORDERED;
      if (!strcmp(str, "striped"))
        return TravParamType::STRIPED;

      outs() << "Error: Unrecognized --trav_type \"" << str << "\"" << endl;
      exit(1);
      return TravParamType::STRIPED;
    }
    static TravParamPrio strtotravprio(const char* str)
    {
      if (!strcmp(str, "sfs"))
        return TravParamPrio::SFS;
      if (!strcmp(str, "bfs"))
        return TravParamPrio::BFS;
      if (!strcmp(str, "dfs"))
        return TravParamPrio::DFS;

      outs() << "Error: Unrecognized --trav_priority \"" << str << "\"" << endl;
      exit(1);
      return TravParamPrio::SFS;
    }
  };
}

#endif
