package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

/** A boolean value (leaf, terminal). */
public class ExprBoolVal extends ExprVal {
  private boolean val;
  public ExprBoolVal(boolean _val) { val = _val; }
  /** @see com.freqhorn.ExprVal#GetInt() */
  public int GetInt()       { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetReal() */
  public double GetReal()   { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetBool() */
  public boolean GetBool()  { return val; }
  /** @see com.freqhorn.ExprVal#GetString() */
  public String GetString() { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetSort() */
  public Expr GetSort()     { return ExprSorts.Bool; }
  public String toString()  { return "" + val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprBoolVal.class)
      return false;
    return GetBool() == ((ExprBoolVal)oth).GetBool();
  }
}
