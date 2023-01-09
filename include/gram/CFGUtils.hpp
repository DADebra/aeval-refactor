#ifndef CFGUTILS__HPP__
#define CFGUTILS__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

#include <sstream>
#include <fstream>

#include "utils/PairHash.hpp"

using namespace ufo;

void CFGUtils::noNtDefError(NT nt, NT root)
{
  outs() << "ERROR: There is no definition for user-defined " <<
    "non-terminal " << nt << " in the CFG for " << root <<
    ". Might be a quantifier variable used outside of a quantifier? Finishing." << endl;
  //assert(0);
}

decltype(CFGUtils::varsNtNameCache) CFGUtils::varsNtNameCache = NULL;
decltype(CFGUtils::constsNtNameCache) CFGUtils::constsNtNameCache = NULL;
decltype(CFGUtils::uniqueVarDeclCache) CFGUtils::uniqueVarDeclCache = NULL;
decltype(CFGUtils::refcnt) CFGUtils::refcnt = 0;
string CFGUtils::sortName(Expr sort)
{
  EZ3 z3(sort->efac());
  string sort_name(z3.toSmtLib(sort));

  // We have a parameterized sort (e.g. Array)
  for (auto&c : sort_name)
  {
    if (c == '(' || c == ')')
      c = '$';
    else if (c == ' ')
      c = '_';
    else
      c = toupper(c);
  }
  return std::move(sort_name);
}

Expr CFGUtils::varsNtName(Expr sort)
{
  if (varsNtNameCache->count(sort) == 0)
  {
    string vars_name(sortName(sort));
    vars_name += "_VARS";
    Expr nt = mkConst(mkTerm(vars_name, sort->efac()), sort);
    return varsNtNameCache->emplace(sort, nt).first->second;
  }
  return varsNtNameCache->at(sort);
}

Expr CFGUtils::constsNtName(Expr sort)
{
  if (constsNtNameCache->count(sort) == 0)
    return constsNtNameCache->emplace(sort,
      mkConst(mkTerm(sortName(sort) + "_CONSTS", sort->efac()), sort)).first->second;
  return constsNtNameCache->at(sort);
}

Expr CFGUtils::uniqueVarDecl(Expr sort)
{
  if (uniqueVarDeclCache->count(sort) == 0)
    return uniqueVarDeclCache->emplace(sort,
      mk<FDECL>(mkTerm(string("Unique-Var"), sort->efac()), sort, sort)).first->second;
  return uniqueVarDeclCache->at(sort);
}

bool CFGUtils::isEither(const Expr& exp)
{
  if (!isOpX<FAPP>(exp))
    return false;
  string expname = lexical_cast<string>(fname(exp)->left());
  return expname == "either";
}

// Returns a set of all quantified variables (which will be used outside
//   of the scope of the quantifier).
// Each variable is an FAPP, for direct re-use.
ExprUSet CFGUtils::getQVars(const Grammar &gram)
{
  ExprUSet qvars;
  unordered_map<Expr,bool> visited;
  function<void(Expr)> qvars_visit = [&] (Expr root)
  {
    if (visited[root])
      return;
    visited[root] = true;

    if (isOpX<FORALL>(root) || isOpX<EXISTS>(root))
    {
      for (int i = 0; i < root->arity() - 1; ++i)
        qvars.insert(fapp(root->arg(i)));
    }

    if (gram.isNt(root))
      for (const auto &prod : gram.prods.at(root))
        qvars_visit(prod);
    else
      for (int i = 0; i < root->arity(); ++i)
        qvars_visit(root->arg(i));
  };
  qvars_visit(gram.root);
  return qvars;
}

string CFGUtils::toSyGuS(Grammar &gram, EZ3 &z3)
{
  ostringstream out;
  // SyGuS requires us to declare the start symbol of the CFG first,
  //   and that production definitions are in the same order as
  //   declarations. Thus, decide on the order first.
  vector<NT> nts;
  nts.push_back(gram.root);
  for (const auto &nt : gram.nts)
    if (nt != gram.root && gram.prods.at(nt).size() != 0)
      nts.push_back(nt);

  // Include quantified variables as uninterpreted non-terminals
  for (auto &qvar : getQVars(gram))
    nts.push_back(qvar);

  unordered_set<Expr> constNts, varNts;
  for (const auto &kv : gram.vars)
  {
    Expr nt = varsNtName(kv.first);
    varNts.insert(nt);
  }
  for (const auto &kv : gram.consts)
  {
    Expr nt = constsNtName(kv.first);
    constNts.insert(nt);
  }

  // Declare non-terminals
  out << "(\n  ";
  for (const auto &nt : nts)
    out << "(" << nt << " " << z3.toSmtLib(typeOf(nt)) << ") ";
  out << ") ";

  // Declare productions
  out << "(\n";
  for (const auto &nt : nts)
  {
    const auto& prods = gram.prods.at(nt);

    // Define corresponding non-terminal (again...)
    out << "    (" << nt << " " << z3.toSmtLib(typeOf(nt)) << " ";
    out << "( "; // Start of productions
    int strpos;
    /*if (constNts.count(nt) != 0)
    {
      // I assume (Constant Int) refers to all valid integers
      out << "(Constant " << z3.toSmtLib(typeOf(nt)) << ") ";
    }
    else if (varNts.count(nt) != 0)
    {
      out << "(Variable " << z3.toSmtLib(typeOf(nt)) << ") ";
    }
    else*/
    {
      for (Expr prod : prods)
      {
        // We allow quantified variables to be used "outside" of their
        // proper scope. CVC5 doesn't. Re-write Expr's of form:
        //   (forall ((favar Int)) (...)) to
        //   (forall ((favar-qvar Int)) (=> (= favar favar-qvar) (...)))
        RW<function<Expr(Expr)>> quantrw(new function<Expr(Expr)>(
          [&gram] (Expr e) -> Expr {
          if (isOpX<FORALL>(e) || isOpX<EXISTS>(e))
          {
            vector<Expr> newquant, conj_eqs;
            for (int i = 0; i < e->arity() - 1; ++i)
            {
              assert(isOpX<FDECL>(e->arg(i)));
              string varname = lexical_cast<string>(e->arg(i)->left());
              Expr newvar = fdecl(
                mkTerm(varname + "-qvar", e->efac()),
                vector<Expr>({e->arg(i)->right()}));
              newquant.push_back(newvar);
              conj_eqs.push_back(mk<EQ>(fapp(e->arg(i)), fapp(newvar)));
            }
            Expr conj = conj_eqs.size() > 1 ?
              mknary<AND>(conj_eqs.begin(), conj_eqs.end()) :
              conj_eqs[0];
            newquant.push_back(mk<IMPL>(conj, e->right()));
            return mknary<FORALL>(newquant.begin(), newquant.end());
          }

          return e;
        }));
        Expr newprod = dagVisit(quantrw, prod);
        out << z3.toSmtLib(newprod) << " ";
      }
    }
    out << "))\n";
  }
  out << "  )\n";

  return std::move(out.str());
}

string CFGUtils::autoGenGram(const CHCs& ruleManager)
{
  stringstream out;
  EZ3 &z3 = ruleManager.m_z3;
  ExprFactory &efac = ruleManager.m_efac;
  SMTUtils u(efac);
  for (const auto& chc : ruleManager.chcs)
  {
    if (!chc.isQuery)
      continue;
    ExprVector cnjs, locCnjs;
    for (auto itr = chc.body->args_begin(); itr != chc.body->args_end(); ++itr)
    {
      if (chc.locVars.size() > 0)
      {
        ExprSet itrVars;
        filter(*itr, bind::IsConst(), inserter(itrVars, itrVars.begin()));
        if (isOp<ComparissonOp>(*itr))
        {
          bool foundTopVar = false;
          for (const auto& var : itrVars)
            if (count(chc.locVars.begin(), chc.locVars.end(), var) &&
                ((*itr)->left() == var || (*itr)->right() == var))
            {
              foundTopVar = true;
              break;
            }
          if (foundTopVar)
          {
            locCnjs.push_back(*itr);
            continue;
          }
        }
      }
      cnjs.push_back(mkNeg(*itr));
    }

    Expr candinv = disjoin(cnjs, efac);
    if (chc.locVars.size() > 0)
    {
      ExprVector existsArgs;
      for (const auto& var : chc.locVars)
        existsArgs.push_back(fname(var));
      if (locCnjs.size() > 0)
        existsArgs.push_back(mk<IMPL>(conjoin(locCnjs, efac), candinv));
      else
        existsArgs.push_back(candinv);
      candinv = mknary<FORALL>(existsArgs);
    }
    //candinv = mkNeg(candinv);
    string relname = lexical_cast<string>(chc.srcRelation);
    out << "(declare-fun " << relname << " () Bool)\n";
    out << "(assert (= " << relname << " ";
    u.print(candinv, out);
    out << "))\n";
  }
  return out.str();
}

TPMethod CFGUtils::strtogenmethod(const char* str)
{
  if (!strcmp(str, "rnd"))
    return TPMethod::RND;
  if (!strcmp(str, "coro"))
    return TPMethod::CORO;
  if (!strcmp(str, "newtrav"))
    return TPMethod::NEWTRAV;
  if (!strcmp(str, "none"))
    return TPMethod::NONE;

  outs() << "Error: Unrecognized --gen_method \"" << str << "\"" << endl;
  exit(1);
  return TPMethod::NONE;
}

TPDir CFGUtils::strtotravdir(const char* str)
{
  if (!strcmp(str, "ltr"))
    return TPDir::LTR;
  if (!strcmp(str, "rtl"))
    return TPDir::RTL;
  if (!strcmp(str, "rnd"))
    return TPDir::RND;
  if (!strcmp(str, "none"))
    return TPDir::NONE;

  outs() << "Error: Unrecognized --trav_direction \"" << str << "\"" << endl;
  exit(1);
  return TPDir::NONE;
}
TPOrder CFGUtils::strtotravord(const char* str)
{
  if (!strcmp(str, "forward"))
    return TPOrder::FOR;
  if (!strcmp(str, "reverse"))
    return TPOrder::REV;
  if (!strcmp(str, "rnd"))
    return TPOrder::RND;
  if (!strcmp(str, "none"))
    return TPOrder::NONE;

  outs() << "Error: Unrecognized --trav_order \"" << str << "\"" << endl;
  exit(1);
  return TPOrder::NONE;
}

TPType CFGUtils::strtotravtype(const char* str)
{
  if (!strcmp(str, "ordered"))
    return TPType::ORDERED;
  if (!strcmp(str, "striped"))
    return TPType::STRIPED;
  if (!strcmp(str, "none"))
    return TPType::NONE;

  outs() << "Error: Unrecognized --trav_type \"" << str << "\"" << endl;
  exit(1);
  return TPType::NONE;
}

TPPrio CFGUtils::strtotravprio(const char* str)
{
  if (!strcmp(str, "sfs"))
    return TPPrio::SFS;
  if (!strcmp(str, "bfs"))
    return TPPrio::BFS;
  if (!strcmp(str, "dfs"))
    return TPPrio::DFS;
  if (!strcmp(str, "none"))
    return TPPrio::NONE;

  outs() << "Error: Unrecognized --trav_priority \"" << str << "\"" << endl;
  exit(1);
  return TPPrio::NONE;
}

#endif
