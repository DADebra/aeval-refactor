package com.freqhorn;

/** An abstract base class for the various value types of an expression.
 * Only use one of {@code GetInt}, {@code GetReal}, {@code GetBool},
 * {@code GetString}: the others will throw an exception.
 * Determine which either via {@code GetSort} here or with the {@code Sort}
 * field of the containing {@code Expr} object.
 */
public abstract class ExprVal {
  public abstract int GetInt();
  public abstract double GetReal();
  public abstract boolean GetBool();
  public abstract String GetString();
  public abstract Expr GetSort();
}
