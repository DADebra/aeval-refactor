#include "deep/RndLearnerV2.hpp"
#include "deep/RndLearnerV3.hpp"

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

const char * getStrValue(const char * opt, const char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      values.push_back(string(argv[i+1]));
    }
  }
}

int main (int argc, char ** argv)
{
  const char *OPT_HELP = "--help";
  const char *OPT_V1 = "--v1";
  const char *OPT_V2 = "--v2";
  const char *OPT_V3 = "--v3";
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_TO = "--to";
  const char *OPT_K_IND = "--kind";
  const char *OPT_ITP = "--itp";
  const char *OPT_BATCH = "--batch";
  const char *OPT_RETRY = "--retry";
  const char *OPT_ELIM = "--skip-elim";
  const char *OPT_OUT_FILE = "--out";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";
  const char *OPT_DATA_LEARNING = "--data";
  const char *OPT_DISJ = "--disj";
  const char *OPT_D1 = "--all-mbp";
  const char *OPT_D2 = "--phase-prop";
  const char *OPT_D3 = "--phase-data";
  const char *OPT_D4 = "--stren-mbp";
  const char *OPT_DEBUG = "--debug";
  const char *OPT_GRAMMAR = "--grammar";
  const char *OPT_GRAM_GEN = "--gen_method";
  const char *OPT_GRAM_MAXREC = "--maxrecdepth";

  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                                 FreqHorn v.0.5 - Copyright (C) 2021                                 * * *\n" <<
        "                                           Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqhorn [--help]               show help\n" <<
        " freqhorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        " " << OPT_V1 << "                            original version (one-by-one sampling)\n"
        " " << OPT_V2 << "                            optimized version for transition systems (+ bootstrapping)\n"
        " " << OPT_V3 << " (default)                  optimized version (+ bootstrapping, propagation, and data candidates)\n"
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        "                                 (if not specified, sample from uniform distributions)\n" <<
        " " << OPT_MAX_ATTEMPTS << " <N>                  maximal number of candidates to sample and check\n" <<
        " " << OPT_TO << "                            timeout for each Z3 run in ms (default: 1000)\n" <<
        " " << OPT_GRAMMAR << " <grammar.smt2>        generate candidates using CFG from `grammar.smt2`\n" <<
        "                                 (can be specified multiple times for inputs with multiple invariants)\n" <<
        " " << OPT_DEBUG << "                         print debugging information during run\n\n" << 
        "V1 options only:\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_K_IND << "                          run k-induction after each learned lemma\n" <<
        " " << OPT_OUT_FILE << " <file.smt2>               serialize invariants to `file.smt2`\n\n" <<
        "V2 options only:\n" <<
        " " << OPT_ITP << "                           bound for itp-based proofs\n" <<
        " " << OPT_BATCH << "                         threshold for how many candidates to check at once\n" <<
        " " << OPT_RETRY << "                         threshold for how many lemmas to wait before giving failures a second chance\n\n" <<
        "V3 options only:\n" <<
        " " << OPT_DATA_LEARNING << "                          bootstrap candidates from behaviors\n" <<
        " " << OPT_ELIM << "                     do not minimize CHC rules (and do not slice)\n\n" <<
        "Grammar options only:\n" <<
        " " << OPT_GRAM_GEN << " <rnd, traverse>    use specified method to generate candidates from grammar\n" <<
        "                                 'rnd' is completely random, 'traverse' will traverse the CFG\n" <<
        " " << OPT_GRAM_MAXREC << " <n>               maximum recursion depth\n\n" <<
        "ImplCheck options only (\"" << OPT_DATA_LEARNING << "\" enabled automatically):\n" <<
        " " << OPT_DISJ << "                          prioritize disjunctive invariants\n" <<
        " " << OPT_D1 << "                       search for phases among all MBPs (needs \"" << OPT_DISJ <<"\")\n" <<
        " " << OPT_D2 << "                    propagate phase lemmas across guards (needs \"" << OPT_DISJ <<"\")\n" <<
        " " << OPT_D3 << "                    datalearn phase lemmas (needs \"" << OPT_DISJ <<"\")\n" <<
        " " << OPT_D4 << "                     strengthen MBP with invariants (needs \"" << OPT_DISJ <<"\")\n";

    return 0;
  }

  bool vers1 = getBoolValue(OPT_V1, false, argc, argv);
  bool vers2 = getBoolValue(OPT_V2, false, argc, argv);
  bool vers3 = getBoolValue(OPT_V3, false, argc, argv);
  if (vers1 + vers2 + vers3 > 1)
  {
    outs() << "Only one version of the algorithm can be chosen\n";
    return 0;
  }

  if (!vers1 && !vers2 && !vers3) vers3 = true; // default

  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  bool debug = getBoolValue(OPT_DEBUG, false, argc, argv);
  int itp = getIntValue(OPT_ITP, 0, argc, argv);
  int batch = getIntValue(OPT_BATCH, 3, argc, argv);
  int retry = getIntValue(OPT_RETRY, 3, argc, argv);
  int do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  const char * outfile = getStrValue(OPT_OUT_FILE, NULL, argc, argv);
  bool do_dl = do_disj || getBoolValue(OPT_DATA_LEARNING, false, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  vector<string> grammars;
  getStrValues(OPT_GRAMMAR, grammars, argc, argv);
  GramParams gramparams = make_tuple(
    CFGUtils::strtogenmethod(getStrValue(OPT_GRAM_GEN, "rnd", argc, argv)),
    getIntValue(OPT_GRAM_MAXREC, 3, argc, argv));

  if (vers3)      // FMCAD'18 + CAV'19 + new experiments
    learnInvariants3(string(argv[argc-1]), grammars, max_attempts, to,
      densecode, aggressivepruning, do_dl, do_elim, do_disj, d_m, d_p, d_d, d_s,
      debug, gramparams);
  else if (vers2) // run the TACAS'18 algorithm
    learnInvariants2(string(argv[argc-1]), grammars, to, outfile,
      max_attempts, itp, batch, retry, densecode, aggressivepruning, debug,
      gramparams);
  else            // run the FMCAD'17 algorithm
    learnInvariants(string(argv[argc-1]), grammars, to, outfile,
      max_attempts, debug, gramparams, kinduction, itp, densecode,
      addepsilon, aggressivepruning);
  
  return 0;
}
