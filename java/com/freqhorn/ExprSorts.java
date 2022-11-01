package com.freqhorn;

import com.freqhorn.Expr;

/** A set of existing sorts to use when making new expressions. */
public class ExprSorts {
    public static final Expr Int = new Expr(ExprOp.INT_TY);
    public static final Expr Bool = new Expr(ExprOp.BOOL_TY);
    public static final Expr Real = new Expr(ExprOp.REAL_TY);
    public static final Expr String = new Expr(ExprOp.STRING_TY);

    /** Return a new array sort of the given types,
     * i.e {@code (array from to)}.
     */
    public static Expr Array(Expr from, Expr to) {
        return new Expr(ExprOp.ARRAY_TY, from, to);
    }
}
