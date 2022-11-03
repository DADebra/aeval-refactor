package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

/** A string value (leaf, terminal). */
public class ExprStringVal extends ExprVal {
  private String val;
  public ExprStringVal(String _val) { val = _val; }
  /** @see com.freqhorn.ExprVal#GetInt() */
  public int GetInt()       { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetReal() */
  public double GetReal()   { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetBool() */
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  /** @see com.freqhorn.ExprVal#GetString() */
  public String GetString() { return val; }
  /** @see com.freqhorn.ExprVal#GetSort() */
  public Expr GetSort()     { return ExprSorts.String; }
  public String toString()  { return val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprStringVal.class)
      return false;
    return GetString().equals(((ExprStringVal)oth).GetString());
  }
}
