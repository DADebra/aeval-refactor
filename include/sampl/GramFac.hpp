#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"
#include "deep/Distribution.hpp"

typedef unordered_set<ufo::Expr> ExprUSet;
typedef unordered_map<ufo::Expr, ufo::Expr> ExprUMap;

#include "gram/ParseTree.hpp"
#include "gram/TravParams.hpp"
#include "gram/CFGUtils.h"
#include "gram/Grammar.h"

#include "gram/CFGUtils.hpp"
#include "gram/Grammar.hpp"
#include "gram/GramEnum.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // A SamplFactory interface to GramEnum
  class GRAMfactory
  {
    private:

    ExprFactory &m_efac;
    EZ3 &z3;

    // Stored for later
    VarMap vars, othervars;
    ConstMap consts;
    TravParams tparams;

    // Whether to print debugging information or not.
    int debug;

    std::shared_ptr<Grammar> gram;

    GramEnum gramenum;

    public:

    bool gramgiven = false;
    bool initialized = false;
    bool done = false;

    private:

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

    public:

    // Whether or not to print candidates before simplification. For debug.
    bool b4simpl;

    GRAMfactory(ExprFactory &_efac, EZ3 &_z3, int _debug) :
      m_efac(_efac), z3(_z3), debug(_debug), gram(new Grammar()), gramenum(*gram, NULL, true) {}

    /*void addVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
    }*/

    void addOtherVar(Expr var)
    {
      othervars[bind::typeOf(var)].insert(var);
    }

    void addIntConst(cpp_int iconst)
    {
      consts[mk<INT_TY>(m_efac)].insert(mkMPZ(iconst, m_efac));
    }

    void addIncVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::INC));
    }

    void addDecVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::DEC));
    }

    void addConstVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::CONST));
    }

    void addUnknownVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(Var(var, VarType::CONST));
    }

    void setParams(TravParams _params)
    {
      assert(!initialized);
      tparams = _params;
    }

    TravParams getParams() { return tparams; }

    // Parse the grammar file. Must be called after addVar(s).
    void initialize(string gram_file, string inv_fname, bool _b4simpl)
    {
      b4simpl = _b4simpl;
      gramenum.b4simpl = b4simpl;
      if (gram_file.empty())
        return;
      *gram = std::move(CFGUtils::parseGramFile(gram_file, inv_fname, z3,
          m_efac, debug, vars, othervars));
      gramgiven = true;
    }

    void extract_consts(const CHCs& chcs)
    {
      ExprUSet nums;
      for (const auto &chc : chcs.chcs)
        filter(chc.body, bind::isNum, inserter(nums, nums.begin()));
      if (debug) outs() << "extract_consts found: ";
      for (const auto& num : nums)
      {
        if (debug) outs() << num << " (type " << typeOf(num) << ") ";
        consts[typeOf(num)].insert(num);
        if (bind::isNum(num))
        {
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

          if (neg)
          {
            if (debug) outs() << neg << " (type " << typeOf(neg) << ") ";
            consts[typeOf(num)].insert(neg);
          }
        }
      }
      if (debug) outs() << endl;
    }

    // Properly initialize *_CONSTS now that we've found them
    void initialize_consts()
    {
      if (!gramgiven)
        return;
      for (const auto &sort_consts : consts)
        for (Expr c : sort_consts.second)
          gram->addConst(c);

      initialized = true;
      gramenum.SetParams(tparams);
    }

    void printSygusGram()
    {
      outs() << CFGUtils::toSyGuS(*gram, z3);
    }

    Expr getFreshCandidate()
    {
      if (gram->root == NULL)
        return NULL; // Should never happen, but handle just in case
      
      Expr ret = gramenum.Increment();
      if (gramenum.IsDone())
        done = true;
      return ret;
    }
  };
}

#endif
