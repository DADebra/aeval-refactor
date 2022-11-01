#ifndef __JNI_GRAMMARPARSER_HPP__
#define __JNI_GRAMMARPARSER_HPP__

#include <utility>

#include "com_freqhorn_GrammarParser.h"

// <sf, inv_fname>
static pair<SamplFactory*,string> constructSamplFac(string program_filename)
{
  ExprFactory *efac = new ExprFactory();
  EZ3 *z3 = new EZ3(*efac);
  CHCs *ruleManager = new CHCs(1000, *efac, *z3);
  pair<SamplFactory*,string> ret(NULL, string());
  if (!ruleManager->parse(program_filename))
    return ret;
  if (ruleManager->decls.size() > 1)
    return ret; // TODO: Implement
  ret.first = new SamplFactory(*efac, *z3, false, 0);
  for (auto &pair : ruleManager->invVars)
    for (int i = 0; i < pair.second.size(); ++i)
      ret.first->addVar(pair.second[i]);
  ret.first->gf.analyze(*ruleManager);
  ret.second = getTerm<string>((*ruleManager->decls.begin())->left());
  return ret;
}

JNIEXPORT jobject JNICALL Java_com_freqhorn_GrammarParser_ParseFromString(
  JNIEnv *env, jclass gpclass, jstring gramstr, jstring progfilename)
{
  auto sf_inv = constructSamplFac(string(env->GetStringUTFChars(progfilename, NULL)));
  if (!sf_inv.first)
    return NULL;
  sf_inv.first->gf.parseGramString(
    string(env->GetStringUTFChars(gramstr, NULL)), sf_inv.second);
  std::shared_ptr<Grammar> gram = sf_inv.first->gf.getGrammar();
  return GrammarToJava(env, *gram);
}

JNIEXPORT jobject JNICALL Java_com_freqhorn_GrammarParser_ParseFromFile(
  JNIEnv *env, jclass gpclass, jstring gramfilename, jstring progfilename)
{
  auto sf_inv = constructSamplFac(string(env->GetStringUTFChars(progfilename, NULL)));
  if (!sf_inv.first)
    return NULL;
  sf_inv.first->gf.parseGramFile(
    string(env->GetStringUTFChars(gramfilename, NULL)), sf_inv.second);
  std::shared_ptr<Grammar> gram = sf_inv.first->gf.getGrammar();
  return GrammarToJava(env, *gram);
}

#endif
