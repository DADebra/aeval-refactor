package com.freqhorn;

import com.freqhorn.Expr;

import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;

/** A context-free grammar which produces {@code Expr}s when traversed.
 */
public class Grammar {
  /** The root of the grammar, a non-terminal. */
  public Expr Root;
  private HashSet<Expr> nts;
  private HashMap<Expr,ArrayList<Expr>> prods;

  private Grammar() {
    nts = new HashSet<Expr>();
    prods = new HashMap<Expr,ArrayList<Expr>>();
  }

  /** Add a new non-terminal with the given name and sort, returning it. */
  public Expr AddNT(String name, Expr sort) {
    Expr ret = Expr.MkVar(name, sort);
    nts.add(ret);
    return ret;
  }
  /** Add a new production at the end of the list of productions for the given
   * non-terminal.
   */
  public void AddProd(Expr nt, Expr prod) {
    if (!prods.containsKey(nt))
      prods.put(nt, new ArrayList<Expr>());
    prods.get(nt).add(prod);
  }
  /** Add a new production at {@code pos} in the list of productions for
   * the given non-terminal.
   */
  public void AddProd(Expr nt, Expr prod, int pos) {
    if (!prods.containsKey(nt))
      prods.put(nt, new ArrayList<Expr>());
    prods.get(nt).add(pos, prod);
  }
  /** Delete the given production from the given non-terminal's productions. */
  public void DelProd(Expr nt, Expr prod) {
    prods.get(nt).remove(prod);
  }
  /** Delete the production at the given position from
   * the given non-terminal's productions.
   */
  public void DelProd(Expr nt, int pos) {
    prods.get(nt).remove(pos);
  }
  /** Return the number of productions that the given non-terminal has. */
  public int GetNumProds(Expr nt) {
    return prods.get(nt).size();
  }
  /** Return the production at position {@code pos} in the
   * given non-terminal's productions.
   */
  public Expr GetProd(Expr nt, int pos) {
    return prods.get(nt).get(pos);
  }

  /** Returns true if the given expression is a non-terminal in this grammar. */
  public boolean IsNT(Expr e) { return nts.contains(e); }

  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append("< NTs = { ");
    boolean firstnt = true;
    for (Expr nt : nts) {
      if (!firstnt)
        ret.append(", ");
      ret.append(nt.toString());
      firstnt = false;
    }
    ret.append(" }, Root = ");
    ret.append(Root.toString());
    ret.append(" >\n");
    for (Expr nt : nts) {
      ret.append("  ");
      ret.append(nt.toString());
      ret.append(" -> ");
      boolean secondprod = false;
      for (Expr prod : prods.get(nt)) {
        if (secondprod)
          ret.append("\n  | ");
        ret.append(prod.toString());
        secondprod = true;
      }
      ret.append("\n");
    }
    return ret.toString();
  }
}
