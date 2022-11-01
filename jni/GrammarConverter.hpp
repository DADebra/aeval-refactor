#ifndef __JNI_GRAMMARCONVERTER_HPP__
#define __JNI_GRAMMARCONVERTER_HPP__

#include <jni.h>

jobject GrammarToJava(JNIEnv *env, const Grammar &gram)
{
  jclass class_gram = env->FindClass("com/freqhorn/Grammar");
  assert(class_gram);
  jmethodID gram_ctor = env->GetMethodID(class_gram, "<init>", "()V");
  assert(gram_ctor);
  jfieldID gram_root = env->GetFieldID(class_gram, "Root", "Lcom/freqhorn/Expr;");
  assert(gram_root);
  jobject ret = env->NewObject(class_gram, gram_ctor);
  assert(ret);
  jobject root = ExprToJava(env, gram.root);
  assert(root);
  env->SetObjectField(ret, gram_root, root);

  jmethodID gram_addnt = env->GetMethodID(class_gram, "AddNT", "(Ljava/lang/String;Lcom/freqhorn/Expr;)Lcom/freqhorn/Expr;");
  assert(gram_addnt);

  unordered_map<Expr,jobject> nt_to_java;
  for (const Expr& nt : gram.nts)
  {
    jstring name = env->NewStringUTF(getTerm<string>(nt->left()->left()).c_str());
    assert(name);
    jobject sort = ExprToJava(env, nt->left()->last());
    assert(sort);
    jobject newnt = env->CallObjectMethod(ret, gram_addnt, name, sort);
    assert(newnt);
    nt_to_java[nt] = newnt;
    assert(nt_to_java[nt]);
  }

  jmethodID gram_addprod = env->GetMethodID(class_gram, "AddProd", "(Lcom/freqhorn/Expr;Lcom/freqhorn/Expr;)V");
  assert(gram_addprod);

  for (const auto& kv : gram.prods)
  {
    const jobject &jnt = nt_to_java[kv.first];
    for (const Expr& prod : kv.second)
    {
      jobject jprod = ExprToJava(env, prod);
      assert(jprod);
      env->CallObjectMethod(ret, gram_addprod, jnt, jprod);
    }
  }

  return ret;
}

#endif
