#ifndef TRAVERSAL__HPP__
#define TRAVERSAL__HPP__

#ifndef GRAMINCLUDED
#error __FILE__ " cannot be included directly. Use '#include \"gram/AllHeaders.hpp\""
#endif

namespace ufo
{

class Traversal
{
  public:

  // Returns true if all candidates in the grammar have been enumerated.
  virtual bool IsDone() { return true; }

  // Returns the candidate at the current traversal position.
  virtual ParseTree GetCurrCand() { return NULL; }

  // Increments the position of this traversal, returning the next candidate
  // (i.e. the candidate at the new position).
  virtual ParseTree Increment() { return NULL; }
};

}
#endif
