
%require "3.2"
%language "c++"
%define api.value.type variant
%define api.token.constructor
%define parse.trace
%define parse.error verbose
%locations

%code requires {
  #include <sstream>

  #include "ufo/Expr.hpp"
  #include "ufo/Smt/EZ3.hh"
  #include "sygus/SynthProblem.hpp"
  #include "gram/AllHeaders.hpp"
}

%parse-param {ufo::SynthProblem& prob} {ufo::ExprFactory& efac} {ufo::EZ3& z3} {ufo::CFGUtils cfgutils}

%token <char> LPAR
%token <char> RPAR
%token <char> USCORE /* Underscore */
%token <std::string> MATCHEDPAR
%token <std::string> ID
%token <std::string> ARRAY
%token <std::string> BITVEC
%token <std::string> CONSTANT
%token <std::string> VARIABLE
%token <std::string> COMMENT
%token <std::string> SETLOGIC
%token <std::string> SYNTHFUN
%token <std::string> SYNTHINV
%token <std::string> DEFFUN
%token <std::string> DECLVAR
%token <std::string> DECLPVAR
%token <std::string> CONSTRAINT
%token <std::string> INVCONSTRAINT
%token <std::string> CHECKSYNTH
%token YYEOF 0

/* %printer { yyo << $$; } <*> */

%{
%}

%code {
namespace yy
{
std::ostringstream toparse; /* Everything we'll eventually send to Z3 parser */
std::unordered_set<std::string> funcs; /* Defined functions */
std::vector<expr::Expr> funcvars; /* Variables for current function */
Grammar gram; /* Current grammar */
std::ostringstream gram_toparse; /* Standard decls we need inside grammar */
bool gram_toparse_hasglobals = false; /* If we've added 'toparse' to 'gram_toparse' */
bool gram_uses_anyconst = false;

yy::location loc;
FILE *infile;
yy::parser::symbol_type yylex()
{
  bool isComment = false;
  char c, nextc;
  std::string s;

  loc.step();

  c = fgetc(infile);
  loc.columns();
  nextc = fgetc(infile);
  ungetc(nextc, infile);

  switch (c)
  {
    case EOF:
      return yy::parser::make_YYEOF(loc);
    case '\n':
      loc.lines();
    case ' ':
    case '\t':
      return yylex();
    case '(':
      return yy::parser::make_LPAR('(', loc);
    case ')':
      return yy::parser::make_RPAR(')', loc);
    case '_':
      if (nextc != ' ' && nextc != '\t' && nextc != '\n')
        break; // Only recognize an independent _ as USCORE
      return yy::parser::make_USCORE('_', loc);
    case ';':
      isComment = true;
      break;
  }

  while (c != ' ' && c != '\n' && c != '\t' && c != ')' && c != '(')
  {
    s += c;
    c = fgetc(infile);
  }
  ungetc(c, infile);
  loc.columns(s.length() - 1);

  if (isComment)
    return yy::parser::make_COMMENT(s, loc);

  if (s == "Array")
    return yy::parser::make_ARRAY(s, loc);
  if (s == "BitVec")
    return yy::parser::make_BITVEC(s, loc);
  if (s == "Constant")
    return yy::parser::make_CONSTANT(s, loc);
  if (s == "Variable")
    return yy::parser::make_VARIABLE(s, loc);
  if (s == "constraint")
    return yy::parser::make_CONSTRAINT(s, loc);
  if (s == "inv-constraint")
    return yy::parser::make_INVCONSTRAINT(s, loc);
  if (s == "check-synth")
    return yy::parser::make_CHECKSYNTH(s, loc);
  if (s == "declare-var")
    return yy::parser::make_DECLVAR(s, loc);
  if (s == "declare-primed-var")
    return yy::parser::make_DECLPVAR(s, loc);
  if (s == "define-fun")
    return yy::parser::make_DEFFUN(s, loc);
  if (s == "set-logic")
    return yy::parser::make_SETLOGIC(s, loc);
  if (s == "synth-fun")
    return yy::parser::make_SYNTHFUN(s, loc);
  if (s == "synth-inv")
    return yy::parser::make_SYNTHINV(s, loc);

  return yy::parser::make_ID(s, loc);
}

void parser::error(const yy::location &loc, const std::string &s)
{
  std::cerr << s << ": " << loc << std::endl;
}

// `vardecls` should include sort at end, and be fdecl's of variable names.
ufo::SynthFunc addFunc(ufo::EZ3& z3, std::string name,
  const std::vector<expr::Expr>& vardecls, expr::Expr sort, ufo::SynthFuncType type)
{
  std::vector<expr::Expr> declArgs;
  for (const expr::Expr& v : vardecls)
  {
    /* FDECL only takes vector of sorts as argument */
    declArgs.push_back(v->right());
  }
  declArgs.push_back(sort);
  /* Z3 needs to know the function exists */
  toparse << "\n(declare-fun " << name << " (";
  for (int i = 0; i < declArgs.size() - 1; ++i)
  {
    expr::Expr vsort = declArgs[i];
    if (i != 0) toparse << " ";
    toparse << z3.toSmtLib(vsort);
  }
  toparse << ") " << z3.toSmtLib(sort) << ")";
  yy::funcs.insert(name);

  ufo::SynthFunc ret;
  if (gram.nts.size() != 0)
    ret = ufo::SynthFunc(type,
      expr::op::bind::fdecl(expr::mkTerm<std::string>(name, sort->efac()),
      declArgs), vardecls, gram, gram_uses_anyconst);
  else
    ret = ufo::SynthFunc(type,
      expr::op::bind::fdecl(expr::mkTerm<std::string>(name, sort->efac()),
      declArgs), vardecls);

  // Reset Grammar
  gram.~Grammar();
  new (&gram) Grammar();
  gram_toparse = ostringstream();
  gram_toparse_hasglobals = false;
  gram_uses_anyconst = false;

  return std::move(ret);
}

expr::Expr prodToExpr(EZ3& z3, const std::string& prodstr)
{
  std::ostringstream parseprod;
  parseprod << gram_toparse.str();
  parseprod << "(assert (= " << prodstr << " " << prodstr << "))";
  Expr ret = z3_from_smtlib(z3, parseprod.str());
  if (!ret)
    return NULL;
  if (isOpX<AND>(ret))
  {
    assert(ret->arity() == 1);
    ret = ret->left();
  }
  assert(isOpX<EQ>(ret));
  assert(ret->arity() == 2);
  return ret->left();
}
}
};

%%

%start sygusfile;

%nterm <std::vector<std::string>> ids;
ids:
    ID ids { std::swap($$, $2); $$.insert($$.begin(), $1); }
    | matchedpar ids { std::swap($$, $2); $$.insert($$.begin(), $1); }
    | USCORE ids { std::swap($$, $2); $$.insert($$.begin(), "_"); }
    | BITVEC ids { std::swap($$, $2); $$.insert($$.begin(), $1); }
    | {}
    ;

%nterm <std::string> matchedpar;
matchedpar:
           LPAR ids RPAR
             {
                if ($2.size() == 1 && yy::funcs.count($2[0]) != 0)
                  /* For some reason, SyGuS uses `(func)` to call a 0-arity
                     function. SMT-LIBv2 uses `func`, so save it that way. */
                  $$ = $2[0];
                else
                {
                  $$ = "(";
                  for (int i = 0; i < $2.size(); ++i)
                  {
                    if (i != 0) $$ += " ";
                    $$ += $2[i];
                  }
                  $$ += ")";
                }
             }
           ;

%nterm <expr::Expr> sort;
sort:
       ID
         {
            if ($1 == "Bool")
              $$ = expr::op::sort::boolTy(efac);
            else if ($1 == "Int")
              $$ = expr::op::sort::intTy(efac);
            else if ($1 == "Real")
              $$ = expr::op::sort::realTy(efac);
            else if ($1 == "String")
              assert(0 && "Strings currently unsupported");
            else
              $$ = expr::mk<expr::op::UNINT_TY>(efac);
         }
       | LPAR ARRAY sort sort RPAR { $$ = expr::op::sort::arrayTy($3, $4); }
       | LPAR USCORE BITVEC ID RPAR { $$ = ufo::op::bv::bvsort(atoi($4.c_str()), efac); }
       ;

%nterm <std::vector<expr::Expr>> vardecls;
vardecls:
         LPAR ID sort RPAR vardecls
           {
              std::swap($$, $5);
              // Note: this can be used directly for quantifiers, NOT for fdecls
              $$.insert($$.begin(), expr::op::bind::constDecl(
                ufo::mkTerm<std::string>($2, efac), $3));
           }
         | {}
         ;

%nterm <std::vector<expr::Expr>> funcvars;
funcvars: vardecls
            {
              std::swap($$, $1);
              funcvars = $$;
              for (const Expr& var : funcvars)
              {
                gram.addVar(expr::op::bind::fapp(var));
                if (!gram_toparse_hasglobals)
                {
                  gram_toparse << toparse.str();
                  gram_toparse_hasglobals = true;
                }
                gram_toparse << z3.toSmtLib(var) << std::endl;
              }
            }

/* Will be parsed by Expr/Z3's parser */
%nterm <std::string> expr;
expr:
     matchedpar
     | ID
     ;

/*For newest version (2.1), but won't work for older versions b/c SR-conflict*/
gramnts:
        LPAR vardecls RPAR
          {
            for (int i = 0; i < $2.size(); ++i)
            {
              NT nt = gram.addNt(expr::op::bind::fapp($2[i]));
              if (i == 0)
                gram.setRoot(nt);
              if (!gram_toparse_hasglobals)
              {
                gram_toparse << toparse.str();
                gram_toparse_hasglobals = true;
              }
              gram_toparse << z3.toSmtLib(nt->left()) << std::endl;
            }
          }
        ;

%nterm <expr::Expr> prod_expr;
prod_expr:
          expr  { $$ = prodToExpr(z3, $1); }
          | LPAR CONSTANT sort RPAR
            {
              $$ = mk<FAPP>(mk<FDECL>(mkTerm(std::string("ANY_CONST"), efac),
                mk<INT_TY>(efac), $3),
                mkTerm(mpz_class(-1), efac));
              gram_uses_anyconst = true;
            }
          | LPAR VARIABLE sort RPAR { $$ = CFGUtils::varsNtName($3); }
          ;

%nterm <std::vector<expr::Expr>> eithers;
eithers:
        prod_expr eithers  { std::swap($$, $2); $$.push_back($1); }
        | prod_expr        { $$.push_back($1); }
        ;

gramprod:
         LPAR ID sort LPAR eithers RPAR RPAR
           {
              NT nt = gram.addNt($2, $3);
              for (const Expr& prod : $5)
                gram.addProd(nt, prod);
           }
         ;

gramprods:
          gramprod gramprods
          | gramprod
          ;

grammar:
        gramnts LPAR gramprods RPAR
        |
        ;

/*
%nterm <std::string> synthdef;
synthdef:
         SYNTHFUN
         | SYNTHINV
         ;
*/

%nterm <std::string> topvardecl;
topvardecl:
        DECLVAR
        | DECLPVAR
        ;

topcommand:
           COMMENT
           | LPAR SETLOGIC ID RPAR { prob._logic = $2; }
           | LPAR SYNTHFUN ID LPAR funcvars RPAR sort grammar RPAR
               {
                  /* TODO: Ignoring grammar for now */
                  prob._synthfuncs.push_back(std::move(
                    addFunc(z3, $3, $5, $7, ufo::SynthFuncType::SYNTH)));
               }
           | LPAR SYNTHINV ID LPAR funcvars RPAR grammar RPAR
               {
                  /* TODO: Ignoring grammar for now */
                  prob._synthfuncs.push_back(std::move(
                    addFunc(z3, $3, $5, expr::op::sort::boolTy(efac),
                      ufo::SynthFuncType::INV)));
               }
           | LPAR DEFFUN ID LPAR vardecls RPAR sort expr RPAR
               {
                  toparse << "\n(define-fun " << $3 << " (";
                  for (int i = 0; i < $5.size(); ++i)
                  {
                    expr::Expr v = $5[i];
                    if (i != 0) toparse << " ";
                    toparse << "(" + expr::getTerm<std::string>(v->left()) <<
                      " " << z3.toSmtLib(v->right()) << ")";
                  }
                  toparse << ") " << z3.toSmtLib($7) << "\n  " << $8 << "\n)";
                  yy::funcs.insert($3);
               }
           | LPAR topvardecl ID sort RPAR
               {
                  std::string sort = z3.toSmtLib($4);
                  toparse << "\n(declare-fun " << $3 << " () " << sort << ")";
                  if ($2 == "declare-primed-var")
                    toparse << "\n(declare-fun " << $3 << "! () " << sort<< ")";
               }
           | LPAR CONSTRAINT expr RPAR
               {
                  toparse << "\n(assert " << $3 << ")";
               }
           | LPAR INVCONSTRAINT ID ID ID ID RPAR { assert(0 && "inv-constraint currently unsupported"); }
           | LPAR CHECKSYNTH RPAR
               {
                  toparse << "\n(assert true)";
                  toparse << "\n(check-sat)";
                  expr::Expr e;
                  try
                  {
                    e = z3_from_smtlib(z3, toparse.str());
                  }
                  catch (...)
                  {
                    //std::cout << "To be parsed: \n" << toparse.str() << std::endl;
                    throw;
                  }
                  if (!e)
                  {
                    fprintf(stderr, "Expr from Z3 is NULL!\n");
                    throw 0;
                  }
                  assert(ufo::isOpX<expr::op::AND>(e));
                  prob._constraints.reserve(e->arity() - 1);
                  for (int i = 0; i < e->arity() - 1; ++i)
                    prob._constraints.push_back(e->arg(i));

                  funcvars.clear();
                  gram.~Grammar();

                  return 0;
               }
           ;

topcommands:
            topcommand
            | topcommand topcommands
            ;

sygusfile:
          topcommands
          ;

%%
