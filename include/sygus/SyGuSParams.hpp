#ifndef __SYGUSPARAMS_HPP__
#define __SYGUSPARAMS_HPP__

#include <boost/logic/tribool.hpp>

#include "utils/CLIParsing.hpp"

#include "gram/TravParams.hpp"

enum class SPMethod { NONE, /*AUTO,*/ SINGLE, ENUM, PRUNE };
SPMethod strtospmethod(const char* str);

struct SyGuSParams
{
  int debug = -1;
  SPMethod method = SPMethod::NONE;
  boost::tribool nonvac = indeterminate;

  SyGuSParams() {}

  SyGuSParams(SPMethod m) : method(m) {}
  SyGuSParams(int argc, char** argv) { FromCLIArgs(argc, argv); SetDefaults(); }

  bool operator==(const SyGuSParams& oth)
  {
    return debug == oth.debug && method == oth.method &&
      bool(nonvac == oth.nonvac);
  }

  bool operator!=(const SyGuSParams& oth)
  {
    return !(*this == oth);
  }

  void SetDefaults()
  {
    if (debug == -1)              debug = 0;
    if (method == SPMethod::NONE) method = SPMethod::SINGLE;
    if (nonvac == indeterminate)  nonvac = false;
  }

  void FromCLIArgs(int argc, char** argv)
  {
    debug = getIntValue("--debug", -1, argc, argv);
    nonvac = getBoolValue("--nonvac", false, argc, argv);
    method = strtospmethod(getStrValue("--sygus-method", "none", argc, argv));
  }

  static void PrintOptionUsage()
  {
    outs() << "  --help                 print this message\n";
    outs() << "  --debug <lvl>          enable debug logging (higher = more)\n";
    outs() << "  --nonvac               don't produce always true/false for predicates\n";
    outs() << "  --sygus-method <single,enum,prune> method of solving problem\n";
  }
};

SPMethod strtospmethod(const char* str)
{
  /*if (!strcmp(str, "auto"))
    return SPMethod::AUTO;*/
  if (!strcmp(str, "single"))
    return SPMethod::SINGLE;
  if (!strcmp(str, "enum"))
    return SPMethod::ENUM;
  if (!strcmp(str, "prune"))
    return SPMethod::PRUNE;
  if (!strcmp(str, "none"))
    return SPMethod::NONE;
  errs() << "Error: Unrecognized --sygus-method \"" << str << "\"" << endl;
  exit(1);
  return SPMethod::NONE;
}
#endif
