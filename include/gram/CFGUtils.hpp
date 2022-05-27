#ifndef CFGUTILS__HPP__
#define CFGUTILS__HPP__

#include "gram/CFGUtils.h"

using namespace ufo;

void CFGUtils::noNtDefError(NT nt, NT root)
{
  outs() << "ERROR: There is no definition for user-defined " <<
    "non-terminal " << nt << " in the CFG for " << root <<
    ". Might be a quantifier variable used outside of a quantifier? Exiting." << endl;
  exit(2);
}

decltype(CFGUtils::varsNtNameCache) CFGUtils::varsNtNameCache;
decltype(CFGUtils::constsNtNameCache) CFGUtils::constsNtNameCache;
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

Expr CFGUtils::varsNtName(Expr sort, VarType type)
{
  auto key = make_pair(sort, type);
  if (varsNtNameCache.count(key) == 0)
  {
    string vars_name(sortName(sort));
    vars_name += "_VARS";
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
    }
    Expr nt = mkConst(mkTerm(vars_name, sort->efac()), sort);
    return varsNtNameCache.emplace(key, nt).first->second;
  }
  return varsNtNameCache.at(key);
}

Expr CFGUtils::constsNtName(Expr sort)
{
  if (constsNtNameCache.count(sort) == 0)
    return constsNtNameCache.emplace(sort,
      mkConst(mkTerm(sortName(sort) + "_CONSTS", sort->efac()), sort)).first->second;
  return constsNtNameCache.at(sort);
}

bool CFGUtils::isEither(const Expr& exp)
{
  if (!isOpX<FAPP>(exp))
    return false;
  string expname = lexical_cast<string>(fname(exp)->left());
  return expname == "either";
}

// exp is e.g. (= iterm iterm), nonterm is e.g. iterm
bool CFGUtils::isRecursive(const Expr& exp, const Expr& nonterm)
{
  // Handle simple recursion
  if (exp == nonterm)
    return true;
  if (isOpX<FDECL>(exp))
    return false; // We don't need to search this deep
  if (isEither(exp))
  {
    // Handle the case of a nested either (e.g. (either 1 (either ...)))
    // We don't want this to be recursive, as this is just a way to
    //   control the traversal and should be equivalent to a non-nested
    //   either.
    return false;
  }
  for (auto itr = exp->args_begin(); itr != exp->args_end(); ++itr)
  {
    if (isRecursive(*itr, nonterm))
      return true;
  }

  return false;
}

Grammar CFGUtils::parseGramFile(string gram_file, string inv_fname, EZ3 &z3,
  ExprFactory &m_efac,int printLog, const VarMap& vars, const VarMap& othervars)
{
  Grammar gram;

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
      for (VarType ty : { VarType::NONE, VarType::UNK, VarType::INC,
      VarType::DEC, VarType::CONST })
        aug_gram << z3.toSmtLib(bind::fname(varsNtName(sort, ty))) << "\n";

      // Generate *_CONSTS declaration
      aug_gram << z3.toSmtLib(bind::fname(constsNtName(sort))) << "\n";

      // Generate *_prio declarations
      aug_gram << "(declare-fun prio (" <<
        sort_smt << " Real) " << sort_smt << ")\n";

      // Generate binary `expands` constraint declarations
      aug_gram << "(declare-fun expands ("<<sort_smt<<" String) Bool)\n";

      // Generate binary `under` constraint declarations
      aug_gram << "(declare-fun under (String "<<sort_smt<<") Bool)\n";
    };

    // We need the Bool eithers for the inv definition (rel is Bool)
    generate_sort_decls(mk<BOOL_TY>(m_efac));

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

    aug_gram << user_cfg.str();

    if (printLog >= 8)
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
        NT newnt = gram.addNt(ex_fname, typeOf(ex->left()));
        if (ex_fname == ANY_INV && !gram.root)
        {
          // Only use ANY_INV if we don't already have a specific one
          gram.setRoot(newnt);
        }
        else if (ex_fname == inv_fname)
        {
          gram.setRoot(newnt);
        }

        Expr prods = ex->right();
        if (!isOpX<FAPP>(prods))
          gram.addProd(newnt, prods);
        else
        {
          string rfname = getTerm<string>(prods->left()->left());
          if (rfname == "prio")
            gram.addProd(newnt, prods->right(),
              getTerm<mpq_class>(prods->last()));
          else if (rfname == "either")
            for (int i = 1; i < prods->arity(); ++i)
            {
              Expr prod = prods->arg(i);
              if (!isOpX<FAPP>(prod))
                gram.addProd(newnt, prod);
              else
              {
                string pname = getTerm<string>(prod->left()->left());
                if (pname == "prio")
                  gram.addProd(newnt, prod->right(), getTerm<mpq_class>(prod->last()));
                else
                  gram.addProd(newnt, prod);
              }
            }
          else
            gram.addProd(newnt, prods);
        }
      }
      else if (isOpX<FAPP>(ex))
      {
        string ename = lexical_cast<string>(bind::fname(ex)->left());
        if (ename == "constraint" || ename == "constraint_any")
        {
          gram.addConstraint(ex->last(), ename == "constraint_any");

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
      }
    }
  }

  //initialized = (inv != NULL);

  if (printLog)
  {
    for (const auto& nt_prods : gram.priomap)
      for (const auto& prod_prio : nt_prods.second)
        outs() << "priomap[<" << nt_prods.first << ", " <<
          prod_prio.first << ">]: " << prod_prio.second << "\n";
  }

  for (const auto& sort_vars : vars)
    for (const auto& var : sort_vars.second)
      gram.addVar(var);

  return std::move(gram);
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
    if (nt != gram.root)
      nts.push_back(nt);

  // Include quantified variables as uninterpreted non-terminals
  for (auto &qvar : getQVars(gram))
    nts.push_back(qvar);

  unordered_set<Expr> constNts, varNts;
  for (const auto &kv : gram.vars)
  {
    nts.push_back(varsNtName(kv.first, VarType::NONE));
    varNts.insert(nts.back());
    unordered_set<VarType> done;
    for (const auto &var : kv.second)
    {
      if (done.count(var.type) != 0) continue;
      nts.push_back(varsNtName(kv.first, var.type));
      varNts.insert(nts.back());
      done.insert(var.type);
    }
  }
  for (const auto &kv : gram.consts)
  {
    nts.push_back(constsNtName(kv.first));
    constNts.insert(nts.back());
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
    if (constNts.count(nt) != 0)
    {
      // I assume (Constant Int) refers to all valid integers
      out << "(Constant " << z3.toSmtLib(typeOf(nt)) << ") ";
    }
    else if (varNts.count(nt) != 0)
    {
      out << "(Variable " << z3.toSmtLib(typeOf(nt)) << ") ";
    }
    else
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


// Returns the path to the CFG (within 'grams') corresponding to invDecl.
// Returns the empty string if no appropriate CFG is found.
// Set 'useany' to only look for ANY_INV.
string CFGUtils::findGram(vector<string>& grams, Expr invDecl, bool useany)
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

TPMethod CFGUtils::strtogenmethod(const char* methodstr)
{
  if (!strcmp(methodstr, "rnd"))
    return TPMethod::RND;
  if (!strcmp(methodstr, "coro"))
    return TPMethod::CORO;
  if (!strcmp(methodstr, "newtrav"))
    return TPMethod::NEWTRAV;

  outs() << "Error: Unrecognized --gen_method \"" << methodstr << "\"" << endl;
  exit(1);
  return TPMethod::RND;
}

TPDir CFGUtils::strtotravdir(const char* str)
{
  if (!strcmp(str, "ltr"))
    return TPDir::LTR;
  if (!strcmp(str, "rtl"))
    return TPDir::RTL;
  if (!strcmp(str, "rnd"))
    return TPDir::RND;

  outs() << "Error: Unrecognized --trav_direction \"" << str << "\"" << endl;
  exit(1);
  return TPDir::LTR;
}
TPOrder CFGUtils::strtotravord(const char* str)
{
  if (!strcmp(str, "forward"))
    return TPOrder::FOR;
  if (!strcmp(str, "reverse"))
    return TPOrder::REV;
  if (!strcmp(str, "rnd"))
    return TPOrder::RND;

  outs() << "Error: Unrecognized --trav_order \"" << str << "\"" << endl;
  exit(1);
  return TPOrder::FOR;
}

TPType CFGUtils::strtotravtype(const char* str)
{
  if (!strcmp(str, "ordered"))
    return TPType::ORDERED;
  if (!strcmp(str, "striped"))
    return TPType::STRIPED;

  outs() << "Error: Unrecognized --trav_type \"" << str << "\"" << endl;
  exit(1);
  return TPType::STRIPED;
}

TPPrio CFGUtils::strtotravprio(const char* str)
{
  if (!strcmp(str, "sfs"))
    return TPPrio::SFS;
  if (!strcmp(str, "bfs"))
    return TPPrio::BFS;
  if (!strcmp(str, "dfs"))
    return TPPrio::DFS;

  outs() << "Error: Unrecognized --trav_priority \"" << str << "\"" << endl;
  exit(1);
  return TPPrio::SFS;
}

#endif
