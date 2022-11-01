package com.freqhorn;

public enum ExprOp {
  // ORDER IMPORTANT
  AND("and"), OR("or"), XOR("xor"), NEG("not"), IMPL("=>"), ITE("ite"),

  PLUS("+"), MINUS("-"), MULT("*"), DIV("/"), MOD("mod"), UN_MINUS("-"),

  EQ("="), NEQ("distinct"), LEQ("<="), GEQ(">="), LT("<"), GT(">"),

  FORALL("forall"), EXISTS("exists"),

  SELECT("select"), STORE("store"), CONST_ARRAY("as-const"),

  FDECL("declare-fun"), FAPP("fapp"),

  INT_TY("Int"), REAL_TY("Real"), BOOL_TY("Bool"), ARRAY_TY("Array"),
  STRING_TY("String");

  private String _op;
  private ExprOp(String __op) { _op = __op; }
  public String op() { return _op; }
  public String toString() { return _op; }

  public Expr GetSort() {
    switch (this) {
      case AND: case OR: case XOR: case NEG: case IMPL: case ITE:
      case EQ: case NEQ: case LEQ: case GEQ: case LT: case GT:
      case FORALL: case EXISTS:
        return ExprSorts.Bool;
    }
    return null;
  }
}
