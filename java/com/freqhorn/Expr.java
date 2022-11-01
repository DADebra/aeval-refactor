package com.freqhorn;

import com.freqhorn.ExprOp;
import com.freqhorn.ExprVal;
import com.freqhorn.ExprStringVal;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * A non-canonicalized expression tree.
 * Modifications can safely be made to these objects
 * without affecting others.
 */
public class Expr {
  private static int nextId = 0;
  private Integer id;
  private ArrayList<Expr> args;
  private Expr parent;

  /**
   * Maps an integer ID to an Expr, where {@code IDMap.get(ex.ID()) == ex}.
   */
  public static HashMap<Integer,Expr> IDMap = new HashMap<Integer,Expr>();

  /**
   * For an expression that has one ({@code IsValue() == false}),
   * the operation (+, -, etc.).
   * Also used for Sort types (e.g. {@code Int} will have
   * {@code Op == ExprOp.INT_TY}).
   * Will be null for expressions with a Value (terminals).
   */
  public ExprOp Op;

  /**
   * The type of the expression, for example: {@code ExprSorts.Int} for
   * {@code +}.
   * Should never be null.
   */
  public Expr Sort;

  /**
   * The value of the expression, if it has one ({@code IsValue() == true}).
   * This will be one of the classes that extends ExprVal:
   * use Sort or Value.getClass() to figure out which accessing method to use.
   */
  public ExprVal Value;

  /**
   * Construct an expression with an operation, for e.g {@code (+ 1 2)}.
   */
  public Expr(ExprOp op, Expr... _args) {
    Op = op; Value = null; parent = null;
    args = new ArrayList<Expr>();
    if (op != null)
      Sort = op.GetSort();
    if (Sort == null && _args.length > 0)
      Sort = _args[_args.length];
    id = nextId++;
    IDMap.put(id, this);
    for (Expr arg : _args)
      if (arg != null) AddArg(arg);
  }

  /**
   * Construct an expression with a value, e.g {@code 1}.
   */
  public Expr(ExprVal value) {
    Op = null; Value = value; Sort = null; parent = null;
    Sort = value.GetSort();
    id = nextId++;
    IDMap.put(id, this);
  }
  /**
   * Internal function for creating variables.
   */
  Expr(ExprVal value, Expr sort) {
    Op = null; Value = value; Sort = sort; parent = null;
    id = nextId++;
    IDMap.put(id, this);
  }

  /** The unique ID of this expression, i.e each unique expression has a unique
   *  ID.
   * However, if {@code e1.ID() != e2.ID()}, then e1 and e2 may be the
   * same expression:
   * think of this like a pointer.
   */
  public Integer ID() { return id; }

  /** The parent of this expression, if present.
   * E.g. for e1 = (+ 1 2), 1.Parent() == e1.
   */
  public Expr Parent() { return parent; }

  /** Returns true if the expression is a terminal. */
  public boolean IsValue() { return Value != null && !IsVar(); }

  /** Returns true if the expression is a variable (or non-terminal). */
  public boolean IsVar() { return Value != null && Value.getClass() == ExprStringVal.class && Sort != null; }

  /** Returns true if the expression is a Sort, like {@code Int}. */
  public boolean IsSort() {
    if (Op == null) return false;
    return Op == ExprOp.INT_TY || Op == ExprOp.BOOL_TY ||
      Op == ExprOp.REAL_TY || Op == ExprOp.STRING_TY ||
      Op == ExprOp.ARRAY_TY;
  }

  /** The number of arguments in the expression, e.g
   * {@code (+ 1 2).ArgSize() == 2}. */
  public int ArgSize() { return args.size(); }
  /** Returns the argument at the given position, e.g
   * {@code (+ 1 2).GetArg(0) == 1}. */
  public Expr GetArg(int pos) { return args.get(pos); }
  /** Returns the first argument, e.g {@code (+ 1 2 3).First() == 1}. */
  public Expr First() { return args.get(0); }
  /** Returns the last argument, e.g {@code (+ 1 2 3).Last() == 3}. */
  public Expr Last() { return args.get(args.size() - 1); }
  /** Add an argument at the given position.
   * Will modify {@code arg}, setting its parent to {@code this}. */
  public void AddArg(int pos, Expr arg) {
    arg.parent = this; args.add(pos, arg);
  }
  /** Add an argument at the end of the current arguments.
   * Will modify {@code arg}, setting its parent to {@code this}. */
  public void AddArg(Expr arg) { arg.parent = this; args.add(arg); }
  /** Delete the argument at position {@code pos}. */
  public Expr DelArg(int pos) {
    Expr arg = args.remove(pos); arg.parent = null; return arg;
  }

  /** Create a variable with the given name/sort, returning it. */
  public static Expr MkVar(String name, Expr sort) {
    return new Expr(new ExprStringVal(name), sort);
  }

  /** Returns the expression as a string in (mostly) SMT-LIBv2. */
  public String toString() {
    if (IsValue() || IsVar())
      return Value.toString();
    StringBuilder ret = new StringBuilder();
    if (!IsSort())
      ret.append("(");
    ret.append(Op.toString());
    for (Expr arg : args) {
      ret.append(" ");
      if (arg != null)
        ret.append(arg.toString());
      else
        ret.append("null");
    }
    if (!IsSort())
      ret.append(")");
    return ret.toString();
  }

  /** Returns true if two expressions are semantically the same expression tree.
   * Ignores differences in ID, parent. */
  public boolean equals(Object _oth) {
    if (_oth.getClass() != Expr.class)
      return false;
    Expr oth = (Expr)_oth;
    if (Op != oth.Op)
      return false;
    if ((Sort == null && oth.Sort != null) ||
        (Sort != null && !Sort.equals(oth.Sort)))
      return false;
    if ((Value == null && oth.Value != null) ||
        (Value != null && Value.equals(oth.Value)))
      return false;
    if ((args == null && oth.args != null) ||
        (args != null && oth.args == null))
      return false;
    if (args == null)
      return true;
    if (args.size() != oth.args.size())
      return false;
    for (int i = 0; i < args.size(); ++i) {
      if ((args.get(i) == null && oth.args.get(i) != null) ||
          (args.get(i) != null && oth.args.get(i) == null))
        return false;
      if (args != null && !args.get(i).equals(oth.args.get(i)))
        return false;
    }
    return true;
  }
}
