#ifndef CFGUTILS__HPP__
#define CFGUTILS__HPP__

#include "gram/CFGUtils.h"

using namespace ufo;

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

    auto generate_sort_decls = [&] (const string& sort_name,
    const string& sort_smt, const string& vars_name)
    {
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

        // Special *_VARS variable
        aug_gram << "(declare-fun " << vars_name << " () " <<
          sort_smt << ")\n";

        // Special *_INC, *_DEC, *_CONST, *_UNKN variables
        for (auto& str : {"_INC", "_DEC", "_CONST", "_UNKN"} )
          aug_gram << "(declare-fun " << vars_name << str << " () " <<
            sort_smt << ")\n";
        // Generate *_prio declarations
        aug_gram << "(declare-fun prio (" <<
          sort_smt << " Real) " << sort_smt << ")\n";

        // Generate binary `expands` constraint declarations
        aug_gram << "(declare-fun expands ("<<sort_smt<<" String) Bool)\n";

        // Generate binary `under` constraint declarations
        aug_gram << "(declare-fun under (String "<<sort_smt<<") Bool)\n";
    };

    // We need the Bool eithers for the inv definition (rel is Bool)
    generate_sort_decls("Bool", "Bool", "BOOL_VARS");

    // Which sorts we've already generated eithers and *_VARS for.
    ExprSet donesorts;
    donesorts.insert(mk<BOOL_TY>(m_efac));

    // Which variables we've already declared.
    ExprUSet donevars;

    // Easiest way to handle all_inv_vars and inv_vars
    auto generate_all = [&] (VarMap vars,
        const char* suffix, bool thisinv)
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

        string vars_name(sort_name);
        vars_name += "_VARS";
        vars_name += suffix;
        for (auto& c : vars_name)
          c = (char)toupper(c);

        // If we haven't already generated an either
        if (donesorts.find(pair.first) == donesorts.end())
        {
          generate_sort_decls(sort_name, sort_smt, vars_name);
          donesorts.insert(pair.first);
        }

        // Generate _FH_* decls for this sort
        for (auto& var : pair.second)
        {
          // var is a FAPP
          if (!donevars.insert(var).second)
            continue;
          aug_gram << z3_to_smtlib(z3, bind::fname(var)) << endl;
        }

        // Only generate definitions for variables of this SamplFactory's invariant
        if (thisinv)
        {
          // Generate definition (i.e. productions) for this sort's *_VARS
          if (pair.second.size() >= 1)
          {
            aug_gram << "(assert (= " << vars_name <<
              " (either";

            for (auto& var : pair.second)
            {
              aug_gram << " " << (Expr)var;
            }

            aug_gram << ")))" << endl;
          }
          else if (pair.second.size() == 1)
          {
            aug_gram << "(assert (= " << vars_name << " " <<
              (Expr)*pair.second.begin() << "))" << endl;
          }
        }
      }
    };

    generate_all(vars, "", true);
    /*generate_all(inv_vars_inc, "_INC", true);
    generate_all(inv_vars_dec, "_DEC", true);
    generate_all(inv_vars_const, "_CONST", true);
    generate_all(inv_vars_unknown, "_UNKN", true);*/
    generate_all(othervars, "", false);

    // Generate INT_CONSTS declaration
    aug_gram << "(declare-fun " << INT_CONSTS << " () Int)\n";

    aug_gram << "(declare-fun constraint (Bool) Bool)\n";
    aug_gram << "(declare-fun constraint_any (Bool) Bool)\n";

    // Generate unary `present` constraint declarations
    aug_gram << "(declare-fun present (String) Bool)\n";

    // Generate unary `maxrecdepth` function declaration
    aug_gram << "(declare-fun maxrecdepth (String) Int)\n";

    aug_gram << user_cfg.str();

    /*if (printLog >= 3)
    {
      outs() << "User-provided grammar:\n";
      outs() << aug_gram.str();
      outs() << endl;
    }*/

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

    // Parse and rewrite priorities
    RW<function<Expr(Expr)>> rw(new function<Expr(Expr)>(
      [&gram] (Expr e) -> Expr
    {
      if (CFGUtils::isEither(e))
      {
        ExprVector newdefargs;
        vector<cpp_rational> rweights;
        for (int i = 1; i < e->arity(); ++i)
        {
          string iname = "";
          if (isOpX<FAPP>(e->arg(i)))
            iname = lexical_cast<string>(bind::fname(e->arg(i))->left());
          if (iname == "prio")
            newdefargs.push_back(e->arg(i)->arg(1));
          else
            newdefargs.push_back(e->arg(i));
        }
        Expr newe = bind::fapp(e->left(), newdefargs);

        for (int i = 1; i < e->arity(); ++i)
        {
          cpp_rational prio;
          string iname = "";
          if (isOpX<FAPP>(e->arg(i)))
            iname = lexical_cast<string>(bind::fname(e->arg(i))->left());
          if (iname == "prio")
          {
            std::pair<Expr,Expr> keypair(newe, e->arg(i)->arg(1));
            prio = lexical_cast<cpp_rational>(e->arg(i)->arg(2));
            gram.priomap[keypair] = prio;
          }
          else
          {
            std::pair<Expr,Expr> keypair(newe, e->arg(i));
            prio = 1.0;
            gram.priomap[keypair] = prio;
          }
          rweights.push_back(prio);
        }

        // Simple GCD, to make sure all priorities convert to integers
        int gcd = 1;
        for (auto &rw : rweights)
          gcd *= (int)denominator(rw);

        vector<int> iweights;
        for (auto &rw : rweights)
          iweights.push_back((int)(rw * gcd));

        gram.distmap.emplace(newe,
          std::move(discrete_distribution<int>(iweights.begin(),
          iweights.end())));

        return newe;
      }
      else
        return e;
    }));
    egram = dagVisit(rw, egram);


    // Find root of grammar and fill in `defs` map.
    for (auto iter = egram->args_begin(); iter != egram->args_end(); ++iter)
    {
      //ex is an assertion
      Expr ex = *iter;
      if (isOpX<EQ>(ex))
      {
        string ex_fname = lexical_cast<string>(bind::fname(ex->left())->left());
        if (ex_fname == ANY_INV && gram.root == NULL)
        {
          // Only use ANY_INV if we don't already have a specific one
          gram.root = ex->left();
        }
        else if (ex_fname == inv_fname)
        {
          gram.root = ex->left();
        }

        gram.defs[ex->left()] = ex->right();
      }
      else if (isOpX<FAPP>(ex))
      {
        string ename = lexical_cast<string>(bind::fname(ex)->left());
        if (ename == "constraint" || ename == "constraint_any")
        {
          gram.constraints.push_back(Constraint(ex));

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
          visitExpr(ex);
        }
      }
    }
  }

  //initialized = (inv != NULL);

  if (printLog)
  {
    for (const auto& p : gram.priomap)
      outs() << "priomap[<" << p.first.first << ", " <<
        p.first.second << ">]: " << p.second << "\n";
    for (const auto& d : gram.distmap)
      outs() << "distmap[" << d.first << "]: " << d.second << "\n";
  }

  gram.vars = vars;

  return gram;
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

    for (int i = 0; i < root->arity(); ++i)
    {
      if (gram.defs.count(root->arg(i)) != 0)
        qvars_visit(gram.defs.at(root->arg(i)));
      qvars_visit(root->arg(i));
    }
  };
  qvars_visit(gram.defs.at(gram.root));
  return qvars;
}

string CFGUtils::toSyGuS(Grammar &gram, EZ3 &z3)
{
  ostringstream out;
  // SyGuS requires us to declare the start symbol of the CFG first,
  //   and that production definitions are in the same order as
  //   declarations. Thus, decide on the order first.
  vector<pair<Expr,Expr>> prods; // Key: nt, Value: production(s)
  prods.push_back(make_pair(gram.root, gram.defs[gram.root]));
  for (auto &pair : gram.defs)
    if (pair.first != gram.root)
      prods.push_back(pair);

  // Include quantified variables as uninterpreted non-terminals
  for (auto &qvar : getQVars(gram))
    prods.push_back(make_pair(qvar, nullptr));

  // Declare non-terminals
  out << "(\n  ";
  for (auto &pair : prods)
    out<<"("<<pair.first<<" "<<z3.toSmtLib(typeOf(pair.first))<<") ";
  out << ") ";

  // Declare productions
  out << "(\n";
  for (auto &pair : prods)
  {
    string nname = lexical_cast<string>(fname(pair.first)->left());

    // Define corresponding non-terminal (again...)
    out<<"    ("<<pair.first<<" "<<z3.toSmtLib(typeOf(pair.first))<<" ";
    out << "( "; // Start of productions
    int strpos;
    if (nname == "INT_CONSTS")
    {
      out << "(Constant Int) ";
    }
    else if ((strpos = nname.rfind("VARS")) > 0 && strpos == nname.length() - 4)
    {
      // nname ends in "VARS", must be a auto-generated non-terminal
      // TODO: Ugly hack
      out << "(Variable " << z3.toSmtLib(typeOf(pair.first)) << ") ";
    }
    else if (pair.second == NULL)
    {
      // I assume (Constant Int) refers to all valid integers
      out << "(Constant " << z3.toSmtLib(typeOf(pair.first)) << ") ";
    }
    else
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

        if (CFGUtils::isEither(e))
        {
          vector<Expr> newargs;
          bool hasEither = false;
          for (int i = 1; i < e->arity(); ++i)
          {
            if (CFGUtils::isEither(e->arg(i)))
            {
              hasEither = true;
              for (int x = 1; x < e->arg(i)->arity(); ++x)
                newargs.push_back(e->arg(i)->arg(x));
            }
            else
              newargs.push_back(e->arg(i));
          }

          if (hasEither)
            return fapp(fname(e), newargs);
          else
            return e;
        }

        return e;
      }));
      Expr prod = dagVisit(quantrw, pair.second);

      if (isOpX<FAPP>(prod))
      {
        string pname = lexical_cast<string>(fname(prod)->left());
        if (pname == "either")
          for (int i = 1; i < prod->arity(); ++i)
            out << z3.toSmtLib(prod->arg(i)) << " ";
        else
          out << z3.toSmtLib(prod) << " ";
      }
      else
        out << z3.toSmtLib(prod);
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
