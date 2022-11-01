package com.freqhorn;

import com.freqhorn.Expr;

import java.util.HashSet;
import java.util.HashMap;
import java.util.ArrayList;

public class Grammar {
  public Expr Root;
  private HashSet<Expr> nts;
  private HashMap<Expr,ArrayList<Expr>> prods;

  private Grammar() {
    nts = new HashSet<Expr>();
    prods = new HashMap<Expr,ArrayList<Expr>>();
  }

  public Expr AddNT(String name, Expr sort) {
    Expr ret = Expr.MkVar(name, sort);
    nts.add(ret);
    return ret;
  }
  public void AddProd(Expr nt, Expr prod) {
    if (!prods.containsKey(nt))
      prods.put(nt, new ArrayList<Expr>());
    prods.get(nt).add(prod);
  }
  public void DelProd(Expr nt, Expr prod) {
    prods.get(nt).remove(prod);
  }
  public void DelProd(Expr nt, int pos) {
    prods.get(nt).remove(pos);
  }
  public int GetNumProds(Expr nt) {
    return prods.get(nt).size();
  }
  public Expr GetProd(Expr nt, int pos) {
    return prods.get(nt).get(pos);
  }

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
