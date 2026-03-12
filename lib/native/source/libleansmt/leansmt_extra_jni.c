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
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1bv_1var(
    JNIEnv* jenv, jclass jcls, jobject jsolver, jstring jname, jint jwidth) {
  (void)jcls;
  if (jsolver == NULL || jname == NULL || jwidth <= 0) {
    return NULL;
  }

  uint64_t solver = bigint_to_u64(jenv, jsolver);
  const char* name = (*jenv)->GetStringUTFChars(jenv, jname, NULL);
  if (name == NULL) {
    return NULL;
  }

  uint64_t result = leansmt_wrapper_mk_bv_var(solver, name, (uint32_t)jwidth);
  (*jenv)->ReleaseStringUTFChars(jenv, jname, name);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1bv_1const(
    JNIEnv* jenv, jclass jcls, jint jwidth, jstring jvalue) {
  (void)jcls;
  if (jvalue == NULL || jwidth <= 0) {
    return NULL;
  }

  const char* value = (*jenv)->GetStringUTFChars(jenv, jvalue, NULL);
  if (value == NULL) {
    return NULL;
  }

  uint64_t result = leansmt_wrapper_mk_bv_const((uint32_t)jwidth, value);
  (*jenv)->ReleaseStringUTFChars(jenv, jvalue, value);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1app1(
    JNIEnv* jenv, jclass jcls, jstring jop, jobject jterm) {
  (void)jcls;
  if (jop == NULL || jterm == NULL) {
    return NULL;
  }

  const char* op = (*jenv)->GetStringUTFChars(jenv, jop, NULL);
  if (op == NULL) {
    return NULL;
  }
  uint64_t term = bigint_to_u64(jenv, jterm);
  uint64_t result = leansmt_wrapper_mk_app1(op, term);
  (*jenv)->ReleaseStringUTFChars(jenv, jop, op);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1app2(
    JNIEnv* jenv, jclass jcls, jstring jop, jobject jlhs, jobject jrhs) {
  (void)jcls;
  if (jop == NULL || jlhs == NULL || jrhs == NULL) {
    return NULL;
  }

  const char* op = (*jenv)->GetStringUTFChars(jenv, jop, NULL);
  if (op == NULL) {
    return NULL;
  }
  uint64_t lhs = bigint_to_u64(jenv, jlhs);
  uint64_t rhs = bigint_to_u64(jenv, jrhs);
  uint64_t result = leansmt_wrapper_mk_app2(op, lhs, rhs);
  (*jenv)->ReleaseStringUTFChars(jenv, jop, op);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1extract(
    JNIEnv* jenv, jclass jcls, jobject jterm, jint jmsb, jint jlsb) {
  (void)jcls;
  if (jterm == NULL || jmsb < 0 || jlsb < 0) {
    return NULL;
  }

  uint64_t term = bigint_to_u64(jenv, jterm);
  uint64_t result = leansmt_wrapper_mk_extract(term, (uint32_t)jmsb, (uint32_t)jlsb);
  return u64_to_bigint(jenv, result);
}

JNIEXPORT jobject JNICALL
Java_org_sosy_1lab_java_1smt_solvers_leansmt_LeanSMTJNI_leansmt_1wrapper_1mk_1indexed_1app1(
    JNIEnv* jenv, jclass jcls, jstring jop, jint jindex, jobject jterm) {
  (void)jcls;
  if (jop == NULL || jterm == NULL || jindex < 0) {
    return NULL;
  }

  const char* op = (*jenv)->GetStringUTFChars(jenv, jop, NULL);
  if (op == NULL) {
    return NULL;
  }
  uint64_t term = bigint_to_u64(jenv, jterm);
  uint64_t result = leansmt_wrapper_mk_indexed_app1(op, (uint32_t)jindex, term);
  (*jenv)->ReleaseStringUTFChars(jenv, jop, op);
  return u64_to_bigint(jenv, result);
}
