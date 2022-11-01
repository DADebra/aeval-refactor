#ifndef __JNI_EXPRCONVERTER_HPP__
#define __JNI_EXPRCONVERTER_HPP__

#include <jni.h>

// ORDER SAME AS IN ExprOp.java
static Operator* op_to_int[] = {
  new AND(), new OR(), new XOR(), new NEG(), new IMPL(), new ITE(),
  new PLUS(), new MINUS(), new MULT(), new DIV(), new MOD(), new UN_MINUS(),
  new EQ(), new NEQ(), new LEQ(), new GEQ(), new LT(), new GT(),
  new FORALL(), new EXISTS(),
  new SELECT(), new STORE(), new CONST_ARRAY(),
  new FDECL(), new FAPP(),
  new INT_TY(), new REAL_TY(), new BOOL_TY(), new ARRAY_TY(), new STRING_TY(), NULL };
static jclass class_expr = NULL, exprOp = NULL;
static jmethodID expr_ctor_val = NULL, expr_ctor_op = NULL,
  expr_ctor_var = NULL, expr_addarg = NULL, expr_tostring;
static jmethodID exprOp_values = NULL;
static jobjectArray exprOp_values_arr = NULL;
static jobjectArray empty_expr_arr = NULL;
static void fillExprStatics(JNIEnv *env)
{
  class_expr = env->FindClass("com/freqhorn/Expr");
  assert(class_expr);

  exprOp = env->FindClass("com/freqhorn/ExprOp");
  assert(exprOp);

  exprOp_values = env->GetStaticMethodID(exprOp, "values", "()[Lcom/freqhorn/ExprOp;");
  assert(exprOp_values);

  exprOp_values_arr = (jobjectArray)env->CallStaticObjectMethod(exprOp, exprOp_values);
  assert(exprOp_values_arr);

  expr_ctor_val = env->GetMethodID(class_expr, "<init>", "(Lcom/freqhorn/ExprVal;)V");
  assert(expr_ctor_val);

  expr_ctor_op = env->GetMethodID(class_expr, "<init>", "(Lcom/freqhorn/ExprOp;[Lcom/freqhorn/Expr;)V");
  assert(expr_ctor_op);

  expr_ctor_var = env->GetMethodID(class_expr, "<init>", "(Lcom/freqhorn/ExprVal;Lcom/freqhorn/Expr;)V");
  assert(expr_ctor_var);

  expr_addarg = env->GetMethodID(class_expr, "AddArg", "(Lcom/freqhorn/Expr;)V");
  assert(expr_addarg);

  expr_tostring = env->GetMethodID(class_expr, "toString", "()Ljava/lang/String;");
  assert(expr_tostring);

  empty_expr_arr = env->NewObjectArray(0, class_expr, NULL);
  assert(empty_expr_arr);
}

jobject ExprToJava(JNIEnv *env, Expr e)
{
  if (!class_expr)
    fillExprStatics(env);

  if (e->arity() == 0)
  {
    // A "value" (i.e. "constant", a leaf)
    if (isOpX<MPZ>(e))
    {
      jclass exprtypeval = env->FindClass("com/freqhorn/ExprIntVal");
      assert(exprtypeval);
      jobject retval = env->AllocObject(exprtypeval);
      assert(retval);
      int val = getTerm<mpz_class>(e).get_si();
      jfieldID valfield = env->GetFieldID(exprtypeval, "val", "I");
      assert(valfield);
      env->SetIntField(retval, valfield, val);
      return env->NewObject(class_expr, expr_ctor_val, retval);
    }
    else if (isOpX<MPQ>(e))
    {
      jclass exprtypeval = env->FindClass("com/freqhorn/ExprRealVal");
      assert(exprtypeval);
      jobject retval = env->AllocObject(exprtypeval);
      assert(retval);
      double val = getTerm<mpq_class>(e).get_d();
      jfieldID valfield = env->GetFieldID(exprtypeval, "val", "D");
      assert(valfield);
      env->SetDoubleField(retval, valfield, val);
      return env->NewObject(class_expr, expr_ctor_val, retval);
    }
    else if (isOpX<STRING>(e))
    {
      jclass exprtypeval = env->FindClass("com/freqhorn/ExprStringVal");
      assert(exprtypeval);
      jobject retval = env->AllocObject(exprtypeval);
      assert(retval);
      jstring val = env->NewStringUTF(getTerm<string>(e).c_str());
      jfieldID valfield = env->GetFieldID(exprtypeval, "val", "Ljava/lang/String;");
      assert(valfield);
      env->SetObjectField(retval, valfield, (jobject)val);
      return env->NewObject(class_expr, expr_ctor_val, retval);
    }
    else if (isOpX<TRUE>(e) || isOpX<FALSE>(e))
    {
      jclass exprtypeval = env->FindClass("com/freqhorn/ExprBoolVal");
      assert(exprtypeval);
      jobject retval = env->AllocObject(exprtypeval);
      assert(retval);
      bool val = isOpX<TRUE>(e);
      jfieldID valfield = env->GetFieldID(exprtypeval, "val", "Z");
      assert(valfield);
      env->SetBooleanField(retval, valfield, val);
      return env->NewObject(class_expr, expr_ctor_val, retval);
    }
    /*else
    {
      errs() << "Can't convert to Java: " << e << endl;
      return NULL;
    }*/
  }
  else if (e->arity() == 1 && isOpX<FAPP>(e))
  {
    // A "variable"
    jclass exprtypeval = env->FindClass("com/freqhorn/ExprStringVal");
    assert(exprtypeval);
    jobject name = env->AllocObject(exprtypeval);
    assert(name);
    jstring val = env->NewStringUTF(getTerm<string>(e->left()->left()).c_str());
    assert(val);
    jfieldID valfield = env->GetFieldID(exprtypeval, "val", "Ljava/lang/String;");
    assert(valfield);
    env->SetObjectField(name, valfield, (jobject)val);

    jobject sort = ExprToJava(env, e->left()->last());
    assert(sort);
    return env->NewObject(class_expr, expr_ctor_var, name, sort);
  }

  int op = -1;
  for (int i = 0; op_to_int[i] != NULL; ++i)
  {
    if (typeid(e->op()) == typeid(*op_to_int[i]))
    {
      op = i;
      break;
    }
  }
  if (op == -1)
  {
    errs() << "Can't convert to Java: " << e << endl;
    return NULL;
  }
  jobject opobj = env->GetObjectArrayElement(exprOp_values_arr, op);
  assert(opobj);

  jobject ret = env->NewObject(class_expr, expr_ctor_op, opobj, empty_expr_arr);
  assert(ret);

  for (int i = 0; i < e->arity(); ++i)
  {
    jobject jarg = ExprToJava(env, e->arg(i));
    assert(jarg);
    env->CallObjectMethod(ret, expr_addarg, jarg);
  }
  return ret;
}

#endif
