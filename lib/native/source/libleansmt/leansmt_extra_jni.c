#include <errno.h>
#include <jni.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "leansmt_wrapper.h"

static uint64_t bigint_to_u64(JNIEnv* jenv, jobject bigint_obj) {
  if (bigint_obj == NULL) {
    return 0;
  }

  jclass bigint_cls = (*jenv)->FindClass(jenv, "java/math/BigInteger");
  if (bigint_cls == NULL) {
    return 0;
  }
  jmethodID to_string = (*jenv)->GetMethodID(jenv, bigint_cls, "toString", "()Ljava/lang/String;");
  if (to_string == NULL) {
    return 0;
  }

  jstring decimal = (jstring)(*jenv)->CallObjectMethod(jenv, bigint_obj, to_string);
  if (decimal == NULL || (*jenv)->ExceptionCheck(jenv)) {
    return 0;
  }

  const char* decimal_chars = (*jenv)->GetStringUTFChars(jenv, decimal, NULL);
  if (decimal_chars == NULL) {
    return 0;
  }

  errno = 0;
  unsigned long long parsed = strtoull(decimal_chars, NULL, 10);
  (*jenv)->ReleaseStringUTFChars(jenv, decimal, decimal_chars);
  if (errno != 0) {
    return 0;
  }
  return (uint64_t)parsed;
}

static jobject u64_to_bigint(JNIEnv* jenv, uint64_t value) {
  jclass bigint_cls = (*jenv)->FindClass(jenv, "java/math/BigInteger");
  if (bigint_cls == NULL) {
    return NULL;
  }
  jmethodID ctor = (*jenv)->GetMethodID(jenv, bigint_cls, "<init>", "(Ljava/lang/String;)V");
  if (ctor == NULL) {
    return NULL;
  }

  char buffer[32];
  (void)snprintf(buffer, sizeof(buffer), "%llu", (unsigned long long)value);
  jstring decimal = (*jenv)->NewStringUTF(jenv, buffer);
  if (decimal == NULL) {
    return NULL;
  }
  return (*jenv)->NewObject(jenv, bigint_cls, ctor, decimal);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1symbol(
    JNIEnv* jenv, jclass jcls, jstring jsymbol) {
  (void)jcls;
  if (jsymbol == NULL) {
    return NULL;
  }

  const char* symbol = (*jenv)->GetStringUTFChars(jenv, jsymbol, NULL);
  if (symbol == NULL) {
    return NULL;
  }
  uint64_t result = leansmt_wrapper_mk_symbol(symbol);
  (*jenv)->ReleaseStringUTFChars(jenv, jsymbol, symbol);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1apply(
    JNIEnv* jenv, jclass jcls, jobject jfn, jobject jarg) {
  (void)jcls;
  if (jfn == NULL || jarg == NULL) {
    return NULL;
  }

  uint64_t fn = bigint_to_u64(jenv, jfn);
  uint64_t arg = bigint_to_u64(jenv, jarg);
  uint64_t result = leansmt_wrapper_mk_apply(fn, arg);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jint JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1declare_1fun(
    JNIEnv* jenv,
    jclass jcls,
    jobject jsolver,
    jstring jname,
    jstring jargSorts,
    jstring jreturnSort) {
  (void)jcls;
  if (jsolver == NULL || jname == NULL || jargSorts == NULL || jreturnSort == NULL) {
    return LEANSMT_ERROR;
  }

  uint64_t solver = bigint_to_u64(jenv, jsolver);
  const char* name = (*jenv)->GetStringUTFChars(jenv, jname, NULL);
  const char* arg_sorts = (*jenv)->GetStringUTFChars(jenv, jargSorts, NULL);
  const char* return_sort = (*jenv)->GetStringUTFChars(jenv, jreturnSort, NULL);
  if (name == NULL || arg_sorts == NULL || return_sort == NULL) {
    if (name != NULL) {
      (*jenv)->ReleaseStringUTFChars(jenv, jname, name);
    }
    if (arg_sorts != NULL) {
      (*jenv)->ReleaseStringUTFChars(jenv, jargSorts, arg_sorts);
    }
    if (return_sort != NULL) {
      (*jenv)->ReleaseStringUTFChars(jenv, jreturnSort, return_sort);
    }
    return LEANSMT_ERROR;
  }

  int result = leansmt_wrapper_declare_fun(solver, name, arg_sorts, return_sort);
  (*jenv)->ReleaseStringUTFChars(jenv, jname, name);
  (*jenv)->ReleaseStringUTFChars(jenv, jargSorts, arg_sorts);
  (*jenv)->ReleaseStringUTFChars(jenv, jreturnSort, return_sort);
  return result;
}

JNIEXPORT jint JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1get_1term_1kind(
    JNIEnv* jenv, jclass jcls, jobject jterm) {
  (void)jcls;
  if (jterm == NULL) {
    return -1;
  }

  uint64_t term = bigint_to_u64(jenv, jterm);
  return (jint)leansmt_wrapper_get_term_kind(term);
}

JNIEXPORT jstring JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1get_1term_1text(
    JNIEnv* jenv, jclass jcls, jobject jterm) {
  (void)jcls;
  if (jterm == NULL) {
    return NULL;
  }

  uint64_t term = bigint_to_u64(jenv, jterm);
  char* text = leansmt_wrapper_get_term_text(term);
  if (text == NULL) {
    return NULL;
  }

  jstring result = (*jenv)->NewStringUTF(jenv, text);
  leansmt_wrapper_free_string(text);
  return result;
}

JNIEXPORT jint JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1get_1term_1num_1children(
    JNIEnv* jenv, jclass jcls, jobject jterm) {
  (void)jcls;
  if (jterm == NULL) {
    return -1;
  }

  uint64_t term = bigint_to_u64(jenv, jterm);
  uint32_t count = leansmt_wrapper_get_term_num_children(term);
  return count == UINT32_MAX ? -1 : (jint)count;
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1get_1term_1child(
    JNIEnv* jenv, jclass jcls, jobject jterm, jint jindex) {
  (void)jcls;
  if (jterm == NULL || jindex < 0) {
    return NULL;
  }

  uint64_t term = bigint_to_u64(jenv, jterm);
  uint64_t child = leansmt_wrapper_get_term_child(term, (uint32_t)jindex);
  if (child == 0) {
    return NULL;
  }
  return u64_to_bigint(jenv, child);
}
