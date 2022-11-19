#ifndef __SYGUSSOLVER_HPP__
#define __SYGUSSOLVER_HPP__

#include <boost/logic/tribool.hpp>

#include "sygus/BaseSolver.hpp"
#include "sygus/SISolver.hpp"
#include "sygus/EnumSolver.hpp"
#include "sygus/PruningSolver.hpp"

namespace ufo
{
using namespace std;
using namespace boost;

class SyGuSSolver : public BaseSolver
{
  private:

  public:

  SyGuSSolver(const SynthProblem &_prob, ExprFactory &_efac, EZ3 &_z3, SyGuSParams p) : BaseSolver(_prob, _efac, _z3, p) {}

  virtual tribool Solve()
  {
    tribool ret;

    if (params.method == SPMethod::SINGLE)
    {
      SISolver sis(prob, efac, z3, params);
      ret = sis.Solve();
      _errmsg = sis.errmsg; _foundfuncs = sis.foundfuncs;
    }
    else if (params.method == SPMethod::ENUM)
    {
      EnumSolver enums(prob, efac, z3, params);
      ret = enums.Solve();
      _errmsg = enums.errmsg; _foundfuncs = enums.foundfuncs;
    }
    else if (params.method == SPMethod::PRUNE)
    {
      PruningSolver prunes(prob, efac, z3, params);
      ret = prunes.Solve();
      _errmsg = prunes.errmsg; _foundfuncs = prunes.foundfuncs;
    }
    else
    {
      _errmsg = "No solving method selected";
      return indeterminate;
    }
    if (!ret || indeterminate(ret))
      return ret;

    if (foundfuncs.size() != prob.synthfuncs.size())
    {
      _errmsg = "[Program Error] Solver invoked on " +
        to_string(prob.synthfuncs.size()) + " functions but only synthesized " +
        to_string(foundfuncs.size()) + " of them";
      return indeterminate;
    }

    findFoundOrdering();

    if (!sanityCheck())
    {
      _errmsg = "[Program Error] Found solutions failed sanity check";
      return indeterminate;
    }

    return true;
  }
};

}

#endif
