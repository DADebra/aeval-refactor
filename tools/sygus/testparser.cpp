#include <cstring>

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"

#include "sygus/SyGuSParser.bison.cpp"

int main(int argc, const char** argv)
{
  expr::ExprFactory efac;
  ufo::EZ3 z3(efac);
  ufo::SynthProblem prob;

  if (argc > 2 || (argc > 1 && !strcmp(argv[1], "--help")))
  {
    printf("Usage: %s [filename]\n", argv[0]);
    return 1;
  }

  if (argc == 2)
    yy::infile = fopen(argv[1], "r");
  else
    yy::infile = stdin;

  yy::parser parse(prob, efac, z3);
  int ret;

  //parse.set_debug_level(9);

  ret = parse();

  return ret;
}
