package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

public class ExprBoolVal extends ExprVal {
  private boolean val;
  public ExprBoolVal(boolean _val) { val = _val; }
  public int GetInt()       { throw new UnsupportedOperationException(); }
  public double GetReal()   { throw new UnsupportedOperationException(); }
  public boolean GetBool()  { return val; }
  public String GetString() { throw new UnsupportedOperationException(); }
  public Expr GetSort()     { return ExprSorts.Bool; }
  public String toString()  { return "" + val; }
  public boolean equals(Object oth) {
    if (oth.getClass() != ExprBoolVal.class)
      return false;
    return GetBool() == ((ExprBoolVal)oth).GetBool();
  }
}
