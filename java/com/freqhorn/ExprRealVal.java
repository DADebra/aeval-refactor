package com.freqhorn;

import com.freqhorn.ExprVal;
import com.freqhorn.ExprSorts;

public class ExprRealVal extends ExprVal {
  private double val;
  public ExprRealVal(double _val) { val = _val; }
  public int GetInt()       { throw new UnsupportedOperationException(); }
  public double GetReal()   { return val; }
  public boolean GetBool()  { throw new UnsupportedOperationException(); }
  public String GetString() { throw new UnsupportedOperationException(); }
  public Expr GetSort()     { return ExprSorts.Real; }
  public String toString()  { return "" + val; }
}
