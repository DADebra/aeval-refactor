#ifndef GRAMFAC__HPP__
#define GRAMFAC__HPP__

#include "ae/ExprSimpl.hpp"
#include "deep/Distribution.hpp"

typedef unordered_set<ufo::Expr> ExprUSet;
typedef unordered_map<ufo::Expr, ufo::Expr> ExprUMap;

#include "gram/AllHeaders.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  enum class VarType { NONE, UNK, INC, DEC, CONST, BITINC, BITDEC };
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

namespace ufo
{
  // A SamplFactory interface to GramEnum
  class GRAMfactory
  {
    private:

    ExprFactory &m_efac;
    EZ3 &z3;
    CFGUtils cfgutils;
    SMTUtils u;

    // Stored for later
    VarMap vars, othervars;
    ConstMap consts;
    TravParams globalparams;
    NTParamMap ntparams;
    unordered_map<Expr, unordered_map<VarType, VarMap::mapped_type>> vars_analyzed;

    Expr precond, postcond;

    // Whether to print debugging information or not.
    int debug;

    std::shared_ptr<Grammar> gram;

    GramEnum gramenum;

    public:

    bool gramgiven = false;
    bool initialized = false;
    bool done = false;

    private:

    void addIncVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::INC].insert(var);
    }

    void addDecVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::DEC].insert(var);
    }

    void addConstVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::CONST].insert(var);
    }

    void addUnknownVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::UNK].insert(var);
    }

    void addBitIncVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::BITINC].insert(var);
    }

    void addBitDecVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
      vars_analyzed[bind::typeOf(var)][VarType::BITDEC].insert(var);
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

    Expr anVarsNtName(Expr sort, VarType type)
    {
      string vars_name(getTerm<string>(CFGUtils::varsNtName(sort)->left()->left()));
      switch (type)
      {
	case VarType::NONE:
	  break;
	case VarType::UNK:
	  vars_name += "_UNK"; break;
	case VarType::INC:
	  vars_name += "_INC"; break;
	case VarType::DEC:
	  vars_name += "_DEC"; break;
	case VarType::CONST:
	  vars_name += "_CONST"; break;
	case VarType::BITINC:
	  vars_name += "_BITINC"; break;
	case VarType::BITDEC:
	  vars_name += "_BITDEC"; break;
      }
      return mkConst(mkTerm(vars_name, sort->efac()), sort);
    }

    // Look for counter variables
    void analyze_vars(const CHCs& chcs)
    {
      for (auto& chc : chcs.chcs)
      {
        if (!chc.isInductive)
          continue; // Not a loop, ignore
        if (chc.srcRelation != chc.dstRelation)
          continue; // Not a loop, ignore
        for (int i = 0; i < chc.srcVars.size(); ++i)
        {
          Expr var = chc.srcVars[i], varprime = chc.dstVars[i];
          Expr vartype = typeOf(var);
          if (isOpX<INT_TY>(vartype))
	  {
            if (u.implies(chc.body, mk<EQ>(varprime, var)))
              addConstVar(var); // Variable which always stays the same
            else if (u.implies(chc.body, mk<GEQ>(varprime, var)))
              addIncVar(var); // Variable which (conditionally) increments
            else if (u.implies(chc.body, mk<LEQ>(varprime, var)))
              addDecVar(var); // Variable which (conditionally) decrements
            else
              addUnknownVar(var); // Variable which does none of the above
          }
          else if (isOpX<BVSORT>(vartype))
          {
            // Check if var is always a power of 2 (or 0)
            Expr bvzero = bv::bvnum(0, bv::width(vartype), var->efac());
            Expr bvone = bv::bvnum(1, bv::width(vartype), var->efac());
            Expr inv = mk<EQ>(bvzero, mk<BAND>(var, mk<BSUB>(var, bvone)));
            if (u.implies(mk<AND>(chc.body, inv), replaceAll(inv, var, varprime)))
            {
              // Is a power of 2 (or 0)
              if (u.implies(chc.body, mk<EQ>(varprime, mk<BSHL>(var, bvone))))
                addBitIncVar(var);
              else if (u.implies(chc.body, mk<EQ>(varprime, mk<BLSHR>(var, bvone))))
                addBitDecVar(var);
              else if (u.implies(chc.body, mk<EQ>(varprime, var)))
                addConstVar(var); // Variable which always stays the same
              else
                addUnknownVar(var); // Variable which does none of the above
            }
            else if (u.implies(chc.body, mk<BUGT>(varprime, var)))
              addIncVar(var); // Variable which always increments
            else if (u.implies(chc.body, mk<BULT>(varprime, var)))
              addDecVar(var); // Variable which always decrements
            else if (u.implies(chc.body, mk<EQ>(varprime, var)))
              addConstVar(var); // Variable which always stays the same
            else
              addUnknownVar(var); // Variable which does none of the above
          }
          else
            addUnknownVar(var);
        }
      }
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

    void extract_postcond(const CHCs& chcs)
    {
      for (const auto& chc : chcs.chcs)
        if (chc.isQuery)
        {
          assert(!postcond);
          postcond = mkNeg(getExists(chc.body, chc.locVars));
        }
    }

    void extract_precond(const CHCs& chcs)
    {
      for (const auto& chc : chcs.chcs)
        if (chc.isFact)
        {
          assert(!precond);
          precond = replaceAll(getExists(chc.body, chc.locVars), chc.dstVars, chcs.invVars.at(chc.dstRelation));
        }
    }

    public:

    // Whether or not to print candidates before simplification. For debug.
    bool b4simpl;

    GRAMfactory(ExprFactory &_efac, EZ3 &_z3, int _debug) :
      m_efac(_efac), z3(_z3), debug(_debug), gram(new Grammar()),
      gramenum(*gram, NULL, DefaultPrunePathFn, debug), u(_efac) {}

    ~GRAMfactory() { Constraint::strcache.clear(); }

    void addVar(Expr var)
    {
      vars[bind::typeOf(var)].insert(var);
    }

    void addOtherVar(Expr var)
    {
      othervars[bind::typeOf(var)].insert(var);
    }

    void addIntConst(cpp_int iconst)
    {
      consts[mk<INT_TY>(m_efac)].insert(mkMPZ(iconst, m_efac));
    }

    void setParams(TravParams _params)
    {
      assert(!initialized);
      globalparams = _params;
    }

    TravParams getParams() { return globalparams; }

    // Parse the grammar file. Must be called after addVar(s).
    void initialize(string gram_file, string inv_fname, bool _b4simpl)
    {
      b4simpl = _b4simpl;
      gramenum.b4simpl = b4simpl;
      if (gram_file.empty())
        return;
      parseGramFile(gram_file, inv_fname);
      gramgiven = true;
    }

    void analyze(const CHCs& chcs)
    {
      analyze_vars(chcs);
      extract_consts(chcs);
      extract_postcond(chcs);
      extract_precond(chcs);
    }

    // Properly initialize *_CONSTS now that we've found them
    void initialize_consts()
    {
      if (!gramgiven)
        return;
      for (const auto &sort_consts : consts)
        for (Expr c : sort_consts.second)
          gram->addConst(c);

      for (const auto& kv : vars)
        for (VarType ty : { VarType::NONE, VarType::UNK, VarType::INC,
        VarType::DEC, VarType::CONST, VarType::BITINC, VarType::BITDEC })
          gram->addNt(anVarsNtName(kv.first, ty));

      for (const auto& kv : vars_analyzed)
        for (const auto& kv2 : kv.second)
        {
          Expr nt = anVarsNtName(kv.first, kv2.first);
          gram->addNt(nt);
          for (const Expr& var : kv2.second)
            gram->addProd(nt, var);
        }

      if (postcond)
        gram->addProd(gram->addNt<BOOL_TY>("POST_COND", m_efac), postcond);
      if (precond)
        gram->addProd(gram->addNt<BOOL_TY>("PRE_COND", m_efac), precond);
      NT precondpart = gram->addNt<BOOL_TY>("PRE_COND_PART", m_efac);
      if (isOpX<AND>(precond))
        for (int i = 0; i < precond->arity(); ++i)
          gram->addProd(precondpart, precond->arg(i));
      else
        gram->addProd(precondpart, precond);

      initialized = true;
      gramenum.SetParams(globalparams, ntparams);
    }

    void printSygusGram()
    {
      outs() << CFGUtils::toSyGuS(*gram, z3);
    }

    int getCurrDepth()
    {
      return gramenum.GetCurrDepth();
    }

    Expr getFreshCandidate()
    {
      if (gram->root == NULL)
        return NULL; // Should never happen, but handle just in case
      
      Expr ret = gramenum.Increment();
      if (gramenum.IsDone())
      {
        outs() << "Unable to find invariant with given grammar and maximum depth." << endl;
        done = true;
      }
      return ret;
    }

    // Call when sampling done
    void finish(bool success)
    {
      if (!initialized)
        return;
      gramenum.Finish(success);
    }

    private:
    bool etob(Expr e) { return isOpX<TRUE>(e); }

    void parseGramFile(string gram_file, string inv_fname)
    {
      // gram_file will be empty if we don't pass `--grammar` option
      if (!gram_file.empty())
      {
	// Read in entire user grammar
	ostringstream user_cfg;
	ifstream infile(gram_file);
	user_cfg << infile.rdbuf();

	// The provided grammar, plus variable definitions and special
	//   variables that we define.
	ostringstream aug_gram;

        // Generate declarations for the `travopt` function
        aug_gram << "(declare-sort TravDir 0)\n";
        aug_gram << "(declare-sort TravOrder 0)\n";
        aug_gram << "(declare-sort TravType 0)\n";
        aug_gram << "(declare-sort TravPrio 0)\n";

        // Generate traversal options
        aug_gram << "(declare-fun ltr () TravDir)\n";
        aug_gram << "(declare-fun rtl () TravDir)\n";
        aug_gram << "(declare-fun forward () TravOrder)\n";
        aug_gram << "(declare-fun reverse () TravOrder)\n";
        aug_gram << "(declare-fun ordered () TravType)\n";
        aug_gram << "(declare-fun striped () TravType)\n";
        aug_gram << "(declare-fun sfs () TravPrio)\n";
        aug_gram << "(declare-fun bfs () TravPrio)\n";
        aug_gram << "(declare-fun dfs () TravPrio)\n";

	// Which sorts we've already generated eithers and *_VARS for.
	ExprSet donesorts;
	auto generate_sort_decls = [&] (Expr sort)
	{
	  if (donesorts.count(sort) != 0)
	    return;
	  donesorts.insert(sort);
	  string sort_smt = z3.toSmtLib(sort);
	  // Generate either functions for given sort
	  for (int i = 1; i <= NUMEITHERS; ++i)
	  {
	    auto gensorts = [&] ()
	    {
	      for (int x = 1; x <= i; ++x)
	      {
		aug_gram << sort_smt << " ";
	      }
	    };
	    aug_gram << "(declare-fun either ( ";
	    gensorts();
	    aug_gram << ") " << sort_smt << ")\n";

	    aug_gram << "(declare-fun either_inorder ( ";
	    gensorts();
	    aug_gram << ") " << sort_smt << ")\n";

	    // Generate n-ary `equal` constraint declarations
	    aug_gram << "(declare-fun equal (";
	    gensorts();
	    aug_gram << ") Bool)\n";

	    // Generate n-ary `equal_under` constraint declarations
	    aug_gram << "(declare-fun equal_under ( String ";
	    gensorts();
	    aug_gram << ") Bool)\n";

	    // Generate n-ary `distinct_under` constraint declarations
	    aug_gram << "(declare-fun distinct_under ( String ";
	    gensorts();
	    aug_gram << ") Bool)\n";
	  }

	  // Generate *_VARS_* declarations
	  /*for (const char* type : { "", "_UNK", "_INC", "_DEC", "_CONST" })
	    aug_gram << "(declare-fun " << bind::fname(varsNtName(sort))->left()
	      << type << " () " << sort_smt << ")\n";*/

          for (VarType ty : { VarType::NONE, VarType::UNK, VarType::INC,
          VarType::DEC, VarType::CONST, VarType::BITINC, VarType::BITDEC })
            aug_gram << z3.toSmtLib(bind::fname(anVarsNtName(sort, ty))) << "\n";

	  // Generate *_CONSTS declaration
	  aug_gram << z3.toSmtLib(bind::fname(CFGUtils::constsNtName(sort))) << "\n";

	  // Generate *_prio declarations
	  aug_gram << "(declare-fun prio (" <<
	    sort_smt << " Real) " << sort_smt << ")\n";

	  // Generate binary `expands` constraint declarations
	  aug_gram << "(declare-fun expands ("<<sort_smt<<" String) Bool)\n";

	  // Generate binary `under` constraint declarations
	  aug_gram << "(declare-fun under (String "<<sort_smt<<") Bool)\n";

          // Generate traversal option declarations
          aug_gram << "(declare-fun trav_direction ("<<sort_smt<<" TravDir Bool) Bool)\n";
          aug_gram << "(declare-fun trav_order ("<<sort_smt<<" TravOrder Bool) Bool)\n";
          aug_gram << "(declare-fun trav_type ("<<sort_smt<<" TravType Bool) Bool)\n";
          aug_gram << "(declare-fun trav_priority ("<<sort_smt<<" TravPrio Bool) Bool)\n";
	};

        // Generate declarations for the standard sorts
	generate_sort_decls(mk<BOOL_TY>(m_efac));
	generate_sort_decls(mk<INT_TY>(m_efac));
	generate_sort_decls(mk<REAL_TY>(m_efac));

	// Which variables we've already declared.
	ExprUSet donevars;

	// Easiest way to handle all_inv_vars and inv_vars
	auto generate_all = [&] (VarMap vars)
	{
	  for (auto& pair : vars)
	  {
	    string sort_smt = z3_to_smtlib<EZ3>(z3, pair.first);

	    generate_sort_decls(pair.first);

	    // Generate _FH_* decls for this sort
	    for (auto& var : pair.second)
	    {
	      // var is a FAPP
	      if (!donevars.insert(var).second)
		continue;
	      aug_gram << z3_to_smtlib(z3, bind::fname(var)) << "\n";
	    }
	  }
	};

	generate_all(vars);
	generate_all(othervars);

	aug_gram << "(declare-fun constraint (Bool) Bool)\n";
	aug_gram << "(declare-fun constraint_any (Bool) Bool)\n";

	// Generate unary `present` constraint declarations
	aug_gram << "(declare-fun present (String) Bool)\n";

	// Generate unary `maxrecdepth` function declaration
	aug_gram << "(declare-fun maxrecdepth (String) Int)\n";

        aug_gram << "(declare-fun POST_COND () Bool)\n";
        aug_gram << "(declare-fun PRE_COND () Bool)\n";
        aug_gram << "(declare-fun PRE_COND_PART () Bool)\n";

	aug_gram << user_cfg.str();

	if (debug >= 8)
	{
	  outs() << "User-provided grammar:\n";
	  outs() << aug_gram.str();
	  outs() << endl;
	}

	// Parse combined grammar
	Expr egram;
	try
	{
	  egram = z3_from_smtlib<EZ3>(z3, aug_gram.str());
	}
	catch (z3::exception e)
	{
	  // Z3 has a nasty habit of printing all of the (either ...)
	  //   functions that we define, leading to thousands of lines of
	  //   output on a parsing failure.
	  // Just print all of the lines up until the listed declarations.
	  string emsg = string(e.msg());
	  int startpos = 0, endpos = emsg.find('\n');
	  if (endpos == string::npos)
	  {
	    errs() << emsg << endl;
	    exit(10);
	  }
	  while (emsg.substr(startpos, 9) != "declared:")
	  {
	    errs() << emsg.substr(startpos, endpos - startpos);
	    startpos = endpos + 1;
	    endpos = emsg.find('\n', startpos);
	    if (endpos == string::npos)
	      break;
	  }
	  errs() << ")" << endl;
	  exit(10);
	}

	if (!egram)
	{
	  errs() << "Invalid grammar file format: No assertions provided" << endl;
	  exit(11);
	}

	if (!isOpX<AND>(egram))
	  // Just for ease of use; WON'T MARSHAL
	  egram = mk<AND>(egram);

	// Find root of grammar and fill in `defs` map.
	for (auto iter = egram->args_begin(); iter != egram->args_end(); ++iter)
	{
	  //ex is an assertion
	  Expr ex = *iter;
	  if (isOpX<EQ>(ex))
	  {
	    if (!isOpX<FAPP>(ex->left()))
	    {
	      errs() << "Invalid format for production: " << ex << endl;
	      assert(0);
	    }
	    string ex_fname = lexical_cast<string>(bind::fname(ex->left())->left());
	    NT newnt = gram->addNt(ex_fname, typeOf(ex->left()));
            if (gram->prods.at(newnt).size() != 0)
            {
              errs() << "Invalid grammar file format: NT \"" << ex_fname << "\" is defined twice." << endl;
              exit(11);
            }
	    if (ex_fname == ANY_INV && !gram->root)
	    {
	      // Only use ANY_INV if we don't already have a specific one
	      gram->setRoot(newnt);
	    }
	    else if (ex_fname == inv_fname)
	    {
	      gram->setRoot(newnt);
	    }

	    Expr prods = ex->right();
	    if (!isOpX<FAPP>(prods))
	      gram->addProd(newnt, prods);
	    else
	    {
	      string rfname = getTerm<string>(prods->left()->left());
	      if (rfname == "prio")
		gram->addProd(newnt, prods->right(),
		  getTerm<mpq_class>(prods->last()));
	      else if (rfname == "either" || rfname == "either_inorder")
              {
		for (int i = 1; i < prods->arity(); ++i)
		{
		  Expr prod = prods->arg(i);
		  if (!isOpX<FAPP>(prod))
		    gram->addProd(newnt, prod);
		  else
		  {
		    string pname = getTerm<string>(prod->left()->left());
		    if (pname == "prio")
		      gram->addProd(newnt, prod->right(), getTerm<mpq_class>(prod->last()));
		    else
		      gram->addProd(newnt, prod);
		  }
		}
                if (rfname == "either_inorder")
                {
                  ntparams[newnt].type = TPType::ORDERED;
                  ntparams[newnt].propagate = false;
                }
              }
	      else
		gram->addProd(newnt, prods);
	    }
	  }
	  else if (isOpX<FAPP>(ex))
	  {
	    string ename = lexical_cast<string>(bind::fname(ex)->left());
	    if (ename == "constraint" || ename == "constraint_any")
	    {
	      gram->addConstraint(ex->last(), ename == "constraint_any");

	      // Parse strings in Z3 now
	      function<void(Expr)> visitExpr = [&] (Expr e)
	      {
		if (isOpX<STRING>(e) && Constraint::strcache.count(e) == 0)
		{
		  string estr = lexical_cast<string>(e);
		  estr = aug_gram.str() + "\n(assert (= "+estr+" "+estr+"))\n";
		  Expr ret = z3_from_smtlib<EZ3>(z3, estr);
		  Constraint::strcache.emplace(e, ret->arg(ret->arity() - 1)->arg(0));
		}
		else
		  for (int i = 0; i < e->arity(); ++i)
		  {
		    if (isOpX<FDECL>(e->arg(i)))
		      continue;
		    visitExpr(e->arg(i));
		  }
	      };
	      visitExpr(ex->last());
	    }
            else if (ename == "trav_direction")
            {
              ntparams[ex->arg(1)].dir = CFGUtils::strtotravdir(getTerm<string>(ex->arg(2)->left()->left()));
              ntparams[ex->arg(1)].propagate = etob(ex->arg(3));
            }
            else if (ename == "trav_order")
            {
              ntparams[ex->arg(1)].order = CFGUtils::strtotravord(getTerm<string>(ex->arg(2)->left()->left()));
              ntparams[ex->arg(1)].propagate = etob(ex->arg(3));
            }
            else if (ename == "trav_type")
            {
              ntparams[ex->arg(1)].type = CFGUtils::strtotravtype(getTerm<string>(ex->arg(2)->left()->left()));
              ntparams[ex->arg(1)].propagate = etob(ex->arg(3));
            }
            else if (ename == "trav_priority")
            {
              ntparams[ex->arg(1)].prio = CFGUtils::strtotravprio(getTerm<string>(ex->arg(2)->left()->left()));
              ntparams[ex->arg(1)].propagate = etob(ex->arg(3));
            }
            else
            {
              errs() << "Unknown top-level assertion \"" << z3.toSmtLib(ex) <<
                "\"" << endl;
              exit(1);
            }
	  }
	}
      }

      //initialized = (inv != NULL);

      if (debug > 2)
      {
	for (const auto& nt_prods : gram->priomap)
	  for (const auto& prod_prio : nt_prods.second)
	    outs() << "priomap[<" << nt_prods.first << ", " <<
	      prod_prio.first << ">]: " << prod_prio.second << "\n";
      }

      for (const auto& sort_vars : vars)
	for (const auto& var : sort_vars.second)
	  gram->addVar(var);
    }
  };
}

#endif
