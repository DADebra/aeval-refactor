
#include <cstdio>
#include <boost/logic/tribool.hpp>

#include "ae/CLIParsing.hpp"
#include "ae/SMTUtils.hpp"
#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "sygus/SynthProblem.hpp"
#include "sygus/SyGuSSolver.hpp"

#include "sygus/SyGuSParser.bison.cpp"

void printUsage()
{
  outs() << "Usage: sygussolver [options] <file.sl>\n";
  outs() << "\n";
  outs() << "Solves the given SyGuS problem specified in SyGuS-IF vers 2.0 format\n";
  outs() << "  Options:\n";
  outs() << "    --help            print this message\n";
  outs() << "    --debug <lvl>     enable debug logging (higher = more)\n";
}

using namespace std;
using namespace ufo;

int main(int argc, char** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1)
  {
    printUsage();
    return 1;
  }

  int debug = getIntValue("--debug", 0, argc, argv);

  char *file = getSyGuSFileName(1, argc, argv);

  if (!file)
  {
    outs() << "No input file specified. Please specify a file in SyGuS format." << endl;
    return 2;
  }

  yy::infile = fopen(file, "r");

  if (!yy::infile)
  {
    errs() << "Error opening input file: " << strerror(errno) << endl;
    return errno;
  }

  ExprFactory efac;
  EZ3 z3(efac);
  SMTUtils u(efac);
  SynthProblem prob;
  yy::parser sygusparser(prob, efac, z3);

  if (debug >= 5)
    sygusparser.set_debug_level(1);

  int ret = sygusparser();

  if (ret)
    return ret;

  SyGuSSolver solver(std::move(prob), efac, z3, debug);
  tribool tret = solver.Solve();
  if (tret)
  {
    for (const auto &kv : solver.foundfuncs)
    {
      outs() << "(define-fun " << kv.first->decl->first() << " (";
      for (int i = 0; i < kv.first->vars.size(); ++i)
      {
        const Expr& var = kv.first->vars[i];
        if (i != 0) outs() << " ";
        outs() << "(" << var->first() << " " << z3.toSmtLib(var->last()) << ")";
      }
      outs() << ") " << z3.toSmtLib(kv.first->decl->last()) << "\n  ";
      u.print(kv.second);
      outs() << "\n)" << endl;
    }
    return 0;
  }
  else if (indeterminate(tret))
  {
    errs() << "Failure: " << solver.errmsg << endl;
    outs() << "fail" << endl; // Comply with SyGuS-IF v2.0
    return 3;
  }
  else
  {
    errs() << "Infeasible: " << solver.errmsg << endl;
    outs() << "infeasible" << endl; // Comply with SyGuS-IF v2.0
    return 4;
  }
}
