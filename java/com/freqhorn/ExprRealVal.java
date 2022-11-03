package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

/** A real (double) value (leaf, terminal). */
public class ExprRealVal extends ExprVal {
  private double val;
  public ExprRealVal(double _val) { val = _val; }
  /** @see com.freqhorn.ExprVal#GetInt() */
  public int GetInt()       { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetReal() */
  public double GetReal()   { return val; }
  /** @see com.freqhorn.ExprVal#GetBool() */
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetString() */
  public String GetString() { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetSort() */
  public Expr GetSort()     { return ExprSorts.Real; }
  public String toString()  { return "" + val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprRealVal.class)
      return false;
    return GetReal() == ((ExprRealVal)oth).GetReal();
  }
}
