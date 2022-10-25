
#include <cstdio>
#include <boost/logic/tribool.hpp>

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "utils/CLIParsing.hpp"
#include "expr/SMTUtils.hpp"
#include "sygus/SynthProblem.hpp"
#include "sygus/SyGuSParams.hpp"
#include "sygus/SyGuSSolver.hpp"

#include "sygus/SyGuSParser.bison.cpp"

void printUsage()
{
  outs() << "Usage: gram2chc -n <size> <file.sl>\n";
  outs() << "\n";
  outs() << "Converts the given SyGuS problem and grammar into a CHC unrealizability problem\n";
  outs() << "\n";
  outs() << "Options:\n";
  outs() << "  -n <size> \t How many variable copies to include in the relation\n";
  outs() << "  --spec \t Generate a spec synthesis problem for relation named 'input' instead\n";
  outs() << "  --debug <size> \t Debug verbosity [0]\n";
  outs().flush();
}

using namespace std;
using namespace ufo;

int printCHC(bool spec, int numcopies, const SynthProblem& prob, ExprFactory& efac, EZ3& z3, CFGUtils& cfgutils);

int main(int argc, char** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1)
  {
    printUsage();
    exit(1);
  }

  int numcopies = getIntValue("-n", -1, argc, argv);
  if (numcopies == -1)
  {
    outs() << "Must specify -n" << endl;
    exit(2);
  }

  bool spec = getBoolValue("--spec", false, argc, argv);

  int debug = getIntValue("--debug", 0, argc, argv);
  SyGuSParams sparams(argc, argv);

  char *file = getSyGuSFileName(1, argc, argv);

  if (!file)
  {
    outs() << "No input file specified. Please specify a file in SyGuS format." << endl;
    exit(2);
  }

  yy::infile = fopen(file, "r");

  if (!yy::infile)
  {
    errs() << "Error opening input file: " << strerror(errno) << endl;
    exit(errno);
  }

  ExprFactory efac;
  EZ3 z3(efac);
  SMTUtils u(efac);
  CFGUtils cfgutils;
  SynthProblem prob;
  yy::parser sygusparser(prob, efac, z3, cfgutils);

  if (debug >= 5)
    sygusparser.set_debug_level(1);

  int ret = sygusparser();

  if (ret)
    exit(ret);

  prob.Analyze();

  return printCHC(spec, numcopies, prob, efac, z3, cfgutils);
}

// Replaces first occurance in a post-fix traversal of 'e'
std::pair<Expr,bool> replaceOne(Expr e, Expr from, Expr to)
{
  ExprVector args;
  if (e == from)
    return make_pair(to, true);

  if (isOpX<FAPP>(e) || isLit(e))
    return make_pair(e, false);

  bool didrepl = false;
  for (int i = 0; i < e->arity(); ++i)
  {
    if (!didrepl)
    {
      auto ret = replaceOne(e->arg(i), from, to);
      if (ret.second)
        didrepl = true;
      args.push_back(ret.first);
    }
    else
      args.push_back(e->arg(i));
  }
  return make_pair(mknary(e->op(), args.begin(), args.end()), didrepl);
}

void nonuniqfilter(const Expr& e, const std::function<bool(Expr)>& filt,
  ExprVector& vec)
{
  if (filt(e))
    vec.push_back(e);
  for (int i = 0; i < e->arity(); ++i)
    nonuniqfilter(e->arg(i), filt, vec);
}

int printCHC(bool spec, int numcopies, const SynthProblem& prob, ExprFactory& efac, EZ3& z3, CFGUtils& cfgutils)
{
  if (prob.gramFuncs.size() != prob.synthfuncs.size())
  {
    outs() << "SyGuS synth-fun's without grammars aren't supported." << endl;
    return 4;
  }
  if (prob.singleapps.size() != prob.synthfuncs.size())
  {
    outs() << "Only single-application functions are supported." << endl;
    return 6;
  }
  if (prob.synthfuncs.size() != 1)
  {
    outs() << "Only one synth-fun is currently supported." << endl;
    return 5;
  }

  SynthFunc &func = prob.synthfuncs[0];
  Grammar &gram = func.gram;
  ExprVector initargs, relargs; // FAPPS
  vector<ExprUMap> varmappings(numcopies), revvarmappings(numcopies);
  ExprUMap ntToRel; // FAPP -> FDECL
  ExprVector rules; // IMPLs
  ExprVector rels; // FDECLs; [0] = fail
  unordered_map<Expr,ExprVector> retcopies;
  auto getretcopy = [&] (const Expr& nt, int i) -> Expr {
    while (retcopies[nt].size() <= i)
      retcopies[nt].push_back(mkConst(mkTerm(z3.toSmtLib(nt) + string("_ret") + to_string(retcopies[nt].size()),
      efac), typeOf(nt)));
    return retcopies[nt][i];
  };

  /*auto printevec = [&] (ExprVector& vec, bool types = false) {
    for (const Expr& e : vec)
      if (types)
        outs() << " " << z3.toSmtLib(typeOf(e));
      else
        outs() << " " << z3.toSmtLib(e);
  };*/
  auto extend = [&] (ExprVector& from, ExprVector& to, bool types = false) {
    for (const Expr& e : to)
      if (types)
        from.push_back(typeOf(e));
      else
        from.push_back(e);
  };

  // Boilerplate
  rels.push_back(constDecl(mkTerm(string("fail"), efac), mk<BOOL_TY>(efac)));

  // Declare input variables
  for (const Expr& v : func.vars)
  {
    for (int i = 0; i < numcopies; ++i)
    {
      relargs.push_back(mkConst(mkTerm(getTerm<string>(v->left()) + to_string(i), efac),
        typeOf(v)));
      if (!spec)
        initargs.push_back(mkConst(mkTerm(getTerm<string>(v->left()) + to_string(i) + "init", efac),
          typeOf(v)));
      /*outs() << "(declare-var " << relargs.back() << " " <<
        z3.toSmtLib(typeOf(v)) << ")\n";*/
      //outs() << z3.toSmtLib(relargs.back()->left()) << "\n";
      varmappings[i][fapp(v)] = relargs.back();
      revvarmappings[i][relargs.back()] = fapp(v);
    }
  }

  // Declare relations
  for (const Expr& nt : gram.nts)
  {
    ExprVector decl;
    decl.push_back(nt->first()->first());
    extend(decl, relargs, true);
    Expr ret = typeOf(nt);
    for (int i = 0; i < numcopies; ++i)
      decl.push_back(ret);
    decl.push_back(mk<BOOL_TY>(efac));
    rels.push_back(mknary<FDECL>(decl));
    ntToRel[nt] = rels.back();
  }

  for (const Expr& nt : gram.nts)
    for (const Expr& prod : gram.prods.at(nt))
    {
      ExprVector deps;
      nonuniqfilter(prod, [&](Expr e){return gram.nts.count(e) != 0;}, deps);
      if (deps.size() == 0)
      {
        // Init(s)
        ExprVector body;
        if (!spec)
          for (int i = 0; i < relargs.size(); ++i)
            body.push_back(mk<EQ>(relargs[i], initargs[i]));
        for (int i = 0; i < numcopies; ++i)
          body.push_back(mk<EQ>(getretcopy(nt, i), replaceAll(prod, varmappings[i])));
        ExprVector relapp;
        relapp.push_back(ntToRel[nt]);
        extend(relapp, relargs);
        for (int i = 0; i < numcopies; ++i)
          relapp.push_back(getretcopy(nt, i));
        rules.push_back(mk<IMPL>(
          conjoin(body, efac),
          mknary<FAPP>(relapp)));
      }
      else
      {
        // Recursive(s)
        ExprVector body;
        for (int di = 0; di < deps.size(); ++di)
        {
          const Expr& d = deps[di];
          ExprVector relapp;
          relapp.push_back(ntToRel[d]);
          extend(relapp, relargs);
          for (int i = 0; i < numcopies; ++i)
            relapp.push_back(getretcopy(d, di*numcopies + i));
          body.push_back(mknary<FAPP>(relapp));
        }
        ExprVector headapp;
        headapp.push_back(ntToRel[nt]);
        extend(headapp, relargs);
        unordered_map<Expr,int> x;
        for (int i = 0; i < numcopies; ++i)
        {
          std::pair<Expr,bool> newprod(prod, true);
          for (int di = 0; di < deps.size(); ++di)
            newprod = replaceOne(newprod.first, deps[di],
              getretcopy(deps[di], di*numcopies + i));
          headapp.push_back(newprod.first);
        }
        rules.push_back(mk<IMPL>(conjoin(body, efac), mknary<FAPP>(headapp)));
      }
    }

  // Query
  {
    Expr allcons = conjoin(prob.constraints, efac);
    ExprVector body;
    ExprVector apps;
    filter(allcons, [&](Expr e){return isOpX<FAPP>(e) && prob.declToFunc.count(e->left()) != 0;},
      inserter(apps, apps.begin()));
    assert(apps.size() == 1);
    Expr app = apps[0];
    ExprVector rootrel;
    rootrel.push_back(ntToRel[gram.root]);
    extend(rootrel, relargs);
    for (int i = 0; i < numcopies; ++i)
    {
      rootrel.push_back(getretcopy(gram.root, i));
      body.push_back(replaceAll(
          replaceAll(allcons, app, getretcopy(gram.root, i)),
          varmappings[i]));
    }
    body.push_back(mknary<FAPP>(rootrel));
    if (spec)
    {
      ExprVector input;
      input.push_back(mkTerm(string("input_spec"), efac));
      extend(input, relargs, true);
      input.push_back(mk<BOOL_TY>(efac));
      rels.push_back(mknary<FDECL>(input));
      ExprVector input_app;
      input_app.push_back(rels.back());
      extend(input_app, relargs);
      body.push_back(mknary<FAPP>(input_app));
    }
    rules.push_back(mk<IMPL>(conjoin(body, efac), fapp(rels[0])));
  }

  auto printvar = [&] (Expr e) {
    if (isOpX<FAPP>(e))
      e = e->left();
    assert(isOpX<FDECL>(e));
    outs() << "(declare-var " << getTerm<string>(e->left());
    outs() << " " << z3.toSmtLib(e->last()) << ")\n";
  };

  if (!spec)
    for (const Expr& e : initargs)
      printvar(e);
  for (const Expr& e : relargs)
    printvar(e);
  for (const auto& kv : retcopies)
    for (const Expr& e : kv.second)
      printvar(e);
  for (const Expr& e : rels)
  {
    outs() << "(declare-rel " << getTerm<string>(e->left()) << " (";
    for (int i = 1; i < e->arity() - 1; ++i)
      outs() << " " << z3.toSmtLib(e->arg(i));
    outs() << " ))\n";
  }

  SMTUtils u(efac);
  for (const Expr& e : rules)
  {
    outs() << "(rule "; u.print(e); outs() << ")\n";
  }

  outs() << "(query fail)\n";

  outs().flush();
  return 0;
}
