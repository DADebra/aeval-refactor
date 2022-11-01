package com.freqhorn;

import com.freqhorn.ExprOp;
import com.freqhorn.ExprVal;
import com.freqhorn.ExprStringVal;

import java.util.ArrayList;
import java.util.HashMap;

/**
 * A non-canonicalized expression tree.
 * <p>
 * Modifications can safely be made to these objects
 * without affecting others.
 */
public class Expr {
  private static int nextId = 0;
  private Integer id;
  private ArrayList<Expr> args;
  private Expr parent;

  public static HashMap<Integer,Expr> IDMap = new HashMap<Integer,Expr>();

  public ExprOp Op;
  public Expr Sort;
  public ExprVal Value;

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
  public Expr(ExprVal value) {
    Op = null; Value = value; Sort = null; parent = null;
    Sort = value.GetSort();
    id = nextId++;
    IDMap.put(id, this);
  }
  Expr(ExprVal value, Expr sort) {
    Op = null; Value = value; Sort = sort; parent = null;
    id = nextId++;
    IDMap.put(id, this);
  }

  public Integer ID() { return id; }
  public Expr Parent() { return parent; }

  public boolean IsValue() { return Value != null && !IsVar(); }
  public boolean IsVar() { return Value != null && Value.getClass() == ExprStringVal.class && Sort != null; }
  public boolean IsSort() {
    if (Op == null) return false;
    return Op == ExprOp.INT_TY || Op == ExprOp.BOOL_TY ||
      Op == ExprOp.REAL_TY || Op == ExprOp.STRING_TY ||
      Op == ExprOp.ARRAY_TY;
  }

  public int ArgSize() { return args.size(); }
  public Expr GetArg(int pos) { return args.get(pos); }
  public Expr First() { return args.get(0); }
  public Expr Last() { return args.get(args.size() - 1); }
  public void AddArg(int pos, Expr arg) {
    arg.parent = this; args.add(pos, arg);
  }
  public void AddArg(Expr arg) { arg.parent = this; args.add(arg); }
  public Expr DelArg(int pos) {
    Expr arg = args.remove(pos); arg.parent = null; return arg;
  }

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

  public static Expr MkVar(String name, Expr sort) {
    return new Expr(new ExprStringVal(name), sort);
  }
}
