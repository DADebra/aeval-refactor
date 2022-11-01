package com.freqhorn;

public abstract class ExprVal {
  public abstract int GetInt();
  public abstract double GetReal();
  public abstract boolean GetBool();
  public abstract String GetString();
  public abstract Expr GetSort();
}
