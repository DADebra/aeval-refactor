
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
  outs() << "Usage: sygussolver [options] <file.sl>\n";
  outs() << "\n";
  outs() << "Solves the given SyGuS problem specified in SyGuS-IF vers 2.0 format\n";
  outs() << "Options:\n";
  SyGuSParams::PrintOptionUsage();
}

using namespace std;
using namespace ufo;

int main(int argc, char** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1)
  {
    printUsage();
    exit(1);
  }

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

  SyGuSSolver solver(std::move(prob), efac, z3, sparams);
  tribool tret = solver.Solve();
  if (tret)
  {
    for (const auto &f : solver.foundfuncsorder)
    {
      outs() << f->GetDefFun(solver.foundfuncs.at(f), u, true) << endl;
    }
    exit(0);
  }
  else if (indeterminate(tret))
  {
    errs() << "Failure: " << solver.errmsg << endl;
    outs() << "fail" << endl; // Comply with SyGuS-IF v2.0
    exit(3);
  }
  else
  {
    errs() << "Infeasible: " << solver.errmsg << endl;
    outs() << "infeasible" << endl; // Comply with SyGuS-IF v2.0
    exit(4);
  }
}
