#ifndef RNDTRAV__HPP__
#define RNDTRAV__HPP__

#include <random>

#include "gram/ParseTree.hpp"
#include "gram/TravParams.hpp"
#include "gram/Grammar.h"

namespace ufo
{

class RndTrav : public Traversal
{

  private:

  Grammar &gram;
  TravParams params;

  ParseTree lastcand;

  default_random_engine randgenerator;

  // qvars is set of quantifier variables for this expression.
  // Using pointer because we need it to be nullable.
  ParseTree getRandCand(const Expr& root, int currdepth,
      std::shared_ptr<ExprUSet> qvars, Expr currnt)
  {
    if (isOpX<FAPP>(root))
    {
      string fname = lexical_cast<string>(bind::fname(root)->left());
      if (gram.vars[bind::typeOf(root)].count(root) != 0)
      {
        // Root is a symbolic variable; don't expand.
        return ParseTree(root);
      }

      // Else, root is a user-defined non-terminal or *either*

      if (fname == "either")
      {
        ParseTree cand = NULL;
        while (!cand)
        {
          // Randomly select from the available productions.
          // Offset by 1 because arg(0) is the fdecl.
          //int randindex = (rand() % (root->arity() - 1)) + 1;
          int randindex = gram.distmap[root](randgenerator) + 1;
          if (CFGUtils::isRecursive(root->arg(randindex), currnt) &&
              currdepth == params.maxrecdepth)
            continue;
          int newdepth = CFGUtils::isRecursive(root->arg(randindex), currnt) ?
                          currdepth + 1 : currdepth;

          cand = getRandCand(root->arg(randindex), newdepth, qvars, currnt);
        }
        return cand;
      }
      else
      {
        // Root is user-defined non-terminal
        if (gram.defs.count(root) != 0)
          return ParseTree(root, vector<ParseTree>{
            getRandCand(gram.defs.at(root), root == currnt ? currdepth : 0, qvars,
            root)}, true);
        else if (qvars != NULL &&
         qvars->count(root->first()) != 0)
          // Root is a variable for a surrounding quantifier
          return ParseTree(root);
        else
        {
          // There's no definition, we're expanding an empty *_VARS
          outs() << "ERROR: There is no definition for user-defined " <<
            "non-terminal " << root << " in the CFG for " << gram.root <<
            ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
          assert(0);
          // We never get here
          return NULL;
        }
      }
    }
    else if (root->arity() == 0)
    {
      // Root is a Z3 terminal, e.g. Int constant, e.g. 3
      return ParseTree(root);
    }

    // Root is Z3-defined non-terminal

    vector<ParseTree> expanded_args;
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

    for (auto itr = root->args_begin();
         itr != root->args_end(); ++itr)
      expanded_args.push_back(getRandCand(*itr, currdepth, localqvars,currnt));

    //return mknary(root->op(), expanded_args.begin(), expanded_args.end());
    return ParseTree(root, expanded_args, false);
  }

  public:

  RndTrav(Grammar &_gram, const TravParams& tp) : gram(_gram), params(tp)
  {
    Increment();
  }

  virtual bool IsDone() { return false; }

  virtual ParseTree GetCurrCand() { return lastcand; }

  virtual ParseTree Increment()
  {
    ParseTree ret = lastcand;
    lastcand = getRandCand(gram.root, 0, NULL, NULL);
    lastcand.fixchildren();
    return ret;
  }
};

}
#endif
