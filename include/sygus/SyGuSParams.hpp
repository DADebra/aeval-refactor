#ifndef __SYGUSPARAMS_HPP__
#define __SYGUSPARAMS_HPP__

#include "utils/CLIParsing.hpp"

#include "gram/TravParams.hpp"

enum class SPMethod { NONE, /*AUTO,*/ SINGLE, ENUM };
SPMethod strtospmethod(const char* str);

struct SyGuSParams
{
  int debug = -1;
  SPMethod method = SPMethod::NONE;

  SyGuSParams() {}

  SyGuSParams(SPMethod m) : method(m) {}
  SyGuSParams(int argc, char** argv) { FromCLIArgs(argc, argv); SetDefaults(); }

  bool operator==(const SyGuSParams& oth)
  {
    return debug == oth.debug && method == oth.method;
  }

  bool operator!=(const SyGuSParams& oth)
  {
    return !(*this == oth);
  }

  void SetDefaults()
  {
    if (debug == -1)              debug = 0;
    if (method == SPMethod::NONE) method = SPMethod::SINGLE;
  }

  void FromCLIArgs(int argc, char** argv)
  {
    debug = getIntValue("--debug", -1, argc, argv);
    method = strtospmethod(getStrValue("--sygus-method", "none", argc, argv));
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
  if (!strcmp(str, "none"))
    return SPMethod::NONE;
  errs() << "Error: Unrecognized --sygus-method \"" << str << "\"" << endl;
  exit(1);
  return SPMethod::NONE;
}
#endif
