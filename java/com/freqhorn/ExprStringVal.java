package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

public class ExprStringVal extends ExprVal {
  private String val;
  public ExprStringVal(String _val) { val = _val; }
  public int GetInt()       { throw new UnsupportedOperationException(); }
  public double GetReal()   { throw new UnsupportedOperationException(); }
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  public String GetString() { return val; }
  public Expr GetSort()     { return ExprSorts.String; }
  public String toString()  { return val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprStringVal.class)
      return false;
    return GetString().equals(((ExprStringVal)oth).GetString());
  }
}
