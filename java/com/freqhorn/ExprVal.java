package com.freqhorn;

/** An abstract base class for the various value types of an expression.
 * <p>
 * Only use one of {@link GetInt}, {@link GetReal}, {@link GetBool},
 * {@link GetString}: the others will throw an exception.
 * Determine which either via {@link GetSort} here or with the {@code Sort}
 * field of the containing {@link Expr} object.
 */
public abstract class ExprVal {
  /** If instanceof ExprIntVal, return the (integer) value. */
  public abstract int GetInt();
  /** If instanceof ExprRealVal, return the (double) value. */
  public abstract double GetReal();
  /** If instanceof ExprBoolVal, return the (boolean) value. */
  public abstract boolean GetBool();
  /** If instanceof ExprStringVal, return the (String) value. */
  public abstract String GetString();
  /** Return the {@link Expr} corresponding to the sort of this value. */
  public abstract Expr GetSort();
}
