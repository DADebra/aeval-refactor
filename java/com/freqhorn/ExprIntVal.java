package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

/** An integer value (leaf, terminal). */
public class ExprIntVal extends ExprVal {
  private int val;
  public ExprIntVal(int _val) { val = _val; }
  /** @see com.freqhorn.ExprVal#GetInt() */
  public int GetInt()       { return val; }
  /** @see com.freqhorn.ExprVal#GetReal() */
  public double GetReal()   { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetBool() */
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetString() */
  public String GetString() { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetSort() */
  public Expr GetSort()     { return ExprSorts.Int; }
  public String toString()  { return "" + val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprIntVal.class)
      return false;
    return GetInt() == ((ExprIntVal)oth).GetInt();
  }
}
