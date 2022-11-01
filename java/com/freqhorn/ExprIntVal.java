package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

public class ExprIntVal extends ExprVal {
  private int val;
  public ExprIntVal(int _val) { val = _val; }
  public int GetInt()       { return val; }
  public double GetReal()   { throw new UnsupportedOperationException(); }
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  public String GetString() { throw new UnsupportedOperationException(); }
  public Expr GetSort()     { return ExprSorts.Int; }
  public String toString()  { return "" + val; }
}
