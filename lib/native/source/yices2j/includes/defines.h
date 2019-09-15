#include <stdlib.h>
#include <jni.h>
#include <gmp.h>
#include "yices.h"


#define CHECK_FOR_NULL(var) \
  if (var == NULL) { \
    return 0; \
  }

typedef void jvoid; // for symmetry to jint, jlong etc.

// Macros for defining JNI functions which call Mathsat
// Use them as follows:
//
// DEFINE_FUNC(java_return_type, escaped_name_without_msat) WITH_X_ARGS(java_arg_types)
// for each arg a definition like STRUCT_ARG(msat_arg_type, position)
// CALLX(msat_return_type, function_name_without_msat)
// return definition like STRUCT_RETURN depending on the return type


#define DEFINE_FUNC(jreturn, func_escaped) \
  JNIEXPORT j##jreturn JNICALL Java_org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi_yices_##func_escaped

#define WITHOUT_ARGS \
  (JNIEnv *jenv, jclass jcls) {

#define WITH_ONE_ARG(jtype) \
  (JNIEnv *jenv, jclass jcls, j##jtype arg1) {

#define WITH_TWO_ARGS(jtype1, jtype2) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2) {

#define WITH_THREE_ARGS(jtype1, jtype2, jtype3) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3) {

#define WITH_FOUR_ARGS(jtype1, jtype2, jtype3, jtype4) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4) {

#define WITH_FIVE_ARGS(jtype1, jtype2, jtype3, jtype4, jtype5) \
  (JNIEnv *jenv, jclass jcls, j##jtype1 arg1, j##jtype2 arg2, j##jtype3 arg3, j##jtype4 arg4, j##jtype5 arg5) {

#define SIMPLE_ARG(mtype, num) \
  mtype m_arg##num = arg##num;

#define UINT32_ARG(num) SIMPLE_ARG(uint32_t, num)

#define NULL_ARG(mtype, num) \
		mtype *m_arg##num = NULL;

#define STRUCT_ARG(mtype, num) \
  if (arg##num == 0) { \
    throwException(jenv, "java/lang/IllegalArgumentException", "Null passed to MathSAT"); \
    return 0; \
  } \
  mtype m_arg##num; \
  m_arg##num.repr = (void *)((size_t)arg##num);

#define STRUCT_ARG_VOID(mtype, num) \
  if (arg##num == 0) { \
    throwException(jenv, "java/lang/IllegalArgumentException", "Null passed to MathSAT"); \
    return; \
  } \
  mtype m_arg##num; \
  m_arg##num.repr = (void *)((size_t)arg##num);

#define STRING_ARG(num) \
  char * m_arg##num = (char *)(*jenv)->GetStringUTFChars(jenv, arg##num, NULL); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

// String argument, possibly null.
#define OPTIONAL_STRING_ARG(num) \
  char * m_arg##num; \
  if (arg##num == NULL) { \
      m_arg##num = NULL; \
  } else { \
      m_arg##num = (char *)(*jenv)->GetStringUTFChars(jenv, arg##num, NULL); \
      if (m_arg##num == NULL) { \
        goto out##num; \
      } \
 }

#define MPZ_ARG(num) \
  mpz_t m_arg##num; \
  char *tmp_str = (char *)(*jenv)->GetStringUTFChars(jenv, arg##num, NULL);\
  mpz_init_set_str(m_arg##num, tmp_str, 10); \
  (*jenv)->ReleaseStringUTFChars(jenv, arg##num, tmp_str);

#define STRUCT_ARRAY_ARG(mtype, num) \
  mtype * m_arg##num; \
  { \
    size_t sz = (size_t)((*jenv)->GetArrayLength(jenv, arg##num)); \
    m_arg##num = (mtype *)malloc(sizeof(mtype) * sz); \
    if (m_arg##num == NULL) { \
      throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for calling Yices"); \
      goto out##num##a; \
    } \
    \
    jlong *tmp = (jlong *)((*jenv)->GetLongArrayElements(jenv, arg##num, NULL)); \
    if (tmp == NULL) { \
      goto out##num##b; \
    } \
    \
    size_t i; \
    for (i = 0; i < sz; ++i) { \
      m_arg##num[i].repr = (void *)((size_t)tmp[i]); \
        if (m_arg##num[i].repr == NULL) { \
        throwException(jenv, "java/lang/IllegalArgumentException", "Null passed to MathSAT"); \
        goto out##num##b; \
      } \
    } \
    (*jenv)->ReleaseLongArrayElements(jenv, arg##num, tmp, 0); \
  }

#define STRUCT_POINTER_ARG(mtype, num) \
  mtype s_arg##num; \
  mtype * m_arg##num = &s_arg##num; 

//may cause memory problems
#define INT_ARRAY_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *)((*jenv)->GetIntArrayElements(jenv, arg##num, NULL)); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

#define EMPTY_INT_ARRAY_ARG(mtype, num) \
  mtype *m_arg##num;\
  size_t sz = (size_t)(arg##num); \
  m_arg##num = (mtype *)malloc(sizeof(mtype) * sz); \
  if (m_arg##num == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for calling Yices"); \
  } \

//may cause memory problems
#define LONG_ARRAY_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *)((*jenv)->GetLongArrayElements(jenv, arg##num, NULL)); \
  if (m_arg##num == NULL) { \
    goto out##num; \
  }

#define POINTER_ARG(mtype, num) \
  mtype * m_arg##num = (mtype *) arg##num;

#define INT_POINTER_ARG(num) \
  int32_t s_arg##num = 0; \
  int32_t *m_arg##num = &s_arg##num;

#define LONG_POINTER_ARG(num) \
  int64_t s_arg##num = 0; \
  int64_t *m_arg##num = &s_arg##num;

#define DOUBLE_POINTER_ARG(num) \
  double s_arg##num = 0; \
  double *m_arg##num = &s_arg##num;

#define TERM_VECTOR_ARG(num) \
  term_vector_t s_arg##num; \
  term_vector_t *m_arg##num = &s_arg##num; \
  yices_init_term_vector(m_arg##num); \

#define STRUCT_ARRAY_OUTPUT_ARG(num) \
  size_t s_arg##num = 0; \
  size_t *m_arg##num = &s_arg##num;

#define MPQ_ARG(num) \
  mpq_t m_arg##num; \
  mpq_init(m_arg##num); \

#define CALL0(mreturn, func) mreturn retval = yices_##func();
#define CALL1(mreturn, func) mreturn retval = yices_##func(m_arg1);
#define CALL2(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2);
#define CALL3(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3);
#define CALL4(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4);
#define CALL5(mreturn, func) mreturn retval = yices_##func(m_arg1, m_arg2, m_arg3, m_arg4, m_arg5);
#define VOID_CALL0(func) yices_##func(); }
#define VOID_CALL1(func) yices_##func(m_arg1); }
#define VOID_CALL2(func) yices_##func(m_arg1, m_arg2); }
#define VOID_CALL2_WITH_RETURN(func) yices_##func(m_arg1, m_arg2);

#define FREE_STRING_OPTIONAL_ARG(num) \
  if(arg##num != NULL) {(*jenv)->ReleaseStringUTFChars(jenv, arg##num, m_arg##num); } \
  out##num:

#define FREE_STRING_ARG(num) \
  (*jenv)->ReleaseStringUTFChars(jenv, arg##num, m_arg##num); \
  out##num:

#define FREE_MPZ_ARG(num) \
  mpz_clear(m_arg##num);

#define FREE_STRUCT_ARRAY_ARG(num) \
  out##num##b: \
  free(m_arg##num); \
  out##num##a:

#define FREE_INT_ARRAY_ARG(num) \
  (*jenv)->ReleaseIntArrayElements(jenv, arg##num, m_arg##num, 0); \
  out##num:

#define FREE_LONG_ARRAY_ARG(num) \
  (*jenv)->ReleaseLongArrayElements(jenv, arg##num, m_arg##num, 0); \
  out##num:

#define PUT_STRUCT_POINTER_ARG(num) \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    (*jenv)->SetLongArrayRegion(jenv, arg##num, 0, 1, (jlong *)&(s_arg##num.repr)); \
  }

#define STRUCT_RETURN \
  if (retval.repr == NULL) { \
    throwException(jenv, "java/lang/IllegalArgumentException", "MathSAT returned null"); \
  } \
  return (jlong)((size_t)(retval.repr)); \
}

#define STRUCT_RETURN_WITH_ENV \
  if (retval.repr == NULL) { \
    const char *msg = msat_last_error_message(m_arg1); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
  } \
  return (jlong)((size_t)(retval.repr)); \
}
//may cause memory leak through yices_error_string
#define INT_RETURN \
   if (retval <= 0 && yices_error_code() != 0){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jint)retval; \
}

#define PLAIN_STRING_RETURN \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, retval); \
  } \
  return jretval; \
}

#define STRING_RETURN \
  if (retval == NULL && yices_error_code()!=0) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return NULL; \
  } \
  PLAIN_STRING_RETURN

#define CONST_STRING_RETURN \
  if (retval == NULL) { \
    const char *msg = msat_last_error_message(m_arg1); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return NULL; \
  } \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, retval); \
  } \
  return jretval; \
}

#define FAILURE_CODE_RETURN \
  if (retval != 0) { \
    const char *msg = msat_last_error_message(m_arg1); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
  } \
}

//may cause memory leak through yices_error_string
#define POINTER_RETURN \
  if(retval == NULL){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return 0; \
  } \
  return (long) retval; \
}
//may cause memory leak through yices_error_string
#define FROM_INT_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jint) *m_arg##num; \
 }

//may cause memory leak through yices_error_string
#define FROM_LONG_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jlong) *m_arg##num; \
 }

#define FROM_DOUBLE_POINTER_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return -1; \
  } \
  return (jdouble) *m_arg##num; \
 }

#define MPQ_RETURN(num) \
  if(retval == -1) { \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
  } \
  char * mpqValue = mpq_get_str(NULL, 10, m_arg##num); \
  if(mpqValue == NULL){ \
    throwException(jenv, "java/lang/NullPointerException", "Result of mpq_get_str was NULL."); \
  } \
  jstring jretval = NULL; \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewStringUTF(jenv, mpqValue); \
  } \
  mpq_clear(m_arg##num); \
  free(mpqValue); \
  return jretval; \
} \

/**
 * This assumes that mathsat allocated an array,
 * returned the pointer and stored the size in the argument arg_num
 * (which was declared with STRUCT_ARRAY_OUTPUT_ARG).
 * It also assumes that the first argument is an environment.
 */
#define RETURN_STRUCT_ARRAY(arg_num) \
  jlongArray jretval = NULL; \
  if ((*jenv)->ExceptionCheck(jenv)) { \
    goto out; \
  } \
  if (retval == NULL) { \
    const char *msg = msat_last_error_message(m_arg1); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    goto out; \
  } \
  \
  jlong *jarr = malloc(sizeof(jlong) * s_arg##arg_num); \
  if (jarr == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Mathsat"); \
    goto out; \
  } \
  size_t i; \
  for (i = 0; i < s_arg##arg_num; ++i) { \
      jarr[i] = (jlong)((size_t)retval[i].repr); \
  } \
  jretval = (*jenv)->NewLongArray(jenv, s_arg##arg_num); \
  if (jretval != NULL) { \
    (*jenv)->SetLongArrayRegion(jenv, jretval, 0, s_arg##arg_num, jarr); \
  } \
  free(jarr); \
  \
  out: \
  msat_free(retval); \
  \
  return jretval; \
}

#define INT_ARRAY_RETURN(num) \
  jintArray jretval = NULL; \
  if(retval == -1){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return jretval; \
    goto out; \
  } \
  if (!(*jenv)->ExceptionCheck(jenv)) { \
    jretval = (*jenv)->NewIntArray(jenv, sz); \
    if(jretval != NULL){ \
      (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, m_arg##num); \
    } \
  } \
  out: \
  free(m_arg##num);\
  return jretval; \
}

#define TERM_VECTOR_ARG_RETURN(num) \
  jintArray jretval = NULL; \
  if ((*jenv)->ExceptionCheck(jenv)) { \
    goto out; \
  } \
  if(retval == -1){ \
    const char *msg = yices_error_string(); \
    throwException(jenv, "java/lang/IllegalArgumentException", msg); \
    return jretval; \
    goto out; \
  } \
  size_t sz = s_arg##num.size; \
  jint *jarr = malloc(sizeof(jint) * sz); \
  if (jarr == NULL) { \
    throwException(jenv, "java/lang/OutOfMemoryError", "Cannot allocate native memory for passing return value from Yices"); \
    goto out; \
  } \
  size_t i; \
  type_t * data = s_arg##num.data; \
  for (i = 0; i < sz; ++i) { \
      jarr[i] = (jint)((size_t)data[i]); \
  } \
  jretval = (*jenv)->NewIntArray(jenv, sz); \
  if (jretval != NULL) { \
    (*jenv)->SetIntArrayRegion(jenv, jretval, 0, sz, jarr); \
  } \
  free(jarr); \
  \
  out: \
  yices_delete_term_vector(m_arg##num); \
  return jretval; \
}

// Define aliases for Yices types
typedef jlong jjctx;
#define CTX_ARG(num) POINTER_ARG(context_t, num)
#define CTX_ARG_VOID(num) POINTER_ARG(context_t, num)
#define CTX_RETURN POINTER_RETURN

typedef jlong jjconf;
#define CONF_ARG(num) POINTER_ARG(ctx_config_t, num)
#define CONF_ARG_VOID(num) POINTER_ARG(ctx_config_t, num)
#define CONF_RETURN POINTER_RETURN

typedef jlong jjparam;
#define PARAM_ARG(num) POINTER_ARG(param_t, num)
#define PARAM_ARG_VOID(num) POINTER_ARG(param_t, num)
#define PARAM_RETURN POINTER_RETURN

// max term count > Integer_MAX_VALUE?
typedef jint jjterm;
#define TERM_ARG(num) SIMPLE_ARG(term_t, num)
#define TERM_ARG_VOID(num) SIMPLE_ARG(term_t, num)
#define TERM_RETURN INT_RETURN

typedef jlong jjmodel;
#define MODEL_ARG(num) POINTER_ARG(model_t, num) //STRUCT_ARG(msat_model, num)
#define MODEL_ARG_VOID(num) POINTER_ARG(model_t, num)//STRUCT_ARG_VOID(msat_model, num)
#define MODEL_RETURN POINTER_RETURN//STRUCT_RETURN_WITH_ENV

typedef jintArray jjtermArray;
#define TERM_ARRAY_ARG(num) INT_ARRAY_ARG(term_t, num) //STRUCT_ARRAY_ARG(term_t, num)
#define FREE_TERM_ARRAY_ARG(num) FREE_INT_ARRAY_ARG(num) //FREE_STRUCT_ARRAY_ARG(num)
#define TERM_ARRAY_OUTPUT_ARG(num) STRUCT_ARRAY_OUTPUT_ARG(num)
#define RETURN_TERM_ARRAY(arg_num) RETURN_STRUCT_ARRAY(arg_num)
#define TERM_POINTER_ARG(num) STRUCT_POINTER_ARG(term_t, num)
#define PUT_TERM_POINTER_ARG(num) PUT_STRUCT_POINTER_ARG(num)

typedef jlong jjdecl;
#define DECL_ARG(num) STRUCT_ARG(msat_decl, num)
#define DECL_RETURN STRUCT_RETURN_WITH_ENV

typedef jlong jjmodel_iterator;
#define MODEL_ITERATOR_ARG(num) STRUCT_ARG(msat_model_iterator, num)
#define MODEL_ITERATOR_ARG_VOID(num) STRUCT_ARG_VOID(msat_model_iterator, num)
#define MODEL_ITERATOR_RETURN STRUCT_RETURN_WITH_ENV

typedef jint jjtype;
#define TYPE_ARG(num) SIMPLE_ARG(type_t, num)
#define TYPE_RETURN INT_RETURN
/*  if (retval == -1){ \
 *   const char *msg = yices_error_string(); \
 *   throwException(jenv, "java/lang/IllegalArgumentException", msg); \
 *   return -1; \
 * } \ 
 *INT_RETURN
 */
// above code might leak memory of error string

typedef jintArray jjtypeArray;
#define TYPE_ARRAY_ARG(num) INT_ARRAY_ARG(type_t, num)//Possible type conflict STRUCT_ARRAY_ARG(type_t, num)
#define FREE_TYPE_ARRAY_ARG(num) FREE_INT_ARRAY_ARG(num)//FREE_STRUCT_ARRAY_ARG(num)
#define TYPE_POINTER_ARG(num) STRUCT_POINTER_ARG(msat_type, num)

typedef jint jjboolean;
#define BOOLEAN_RETURN INT_RETURN
/*    if (retval == 0 && yices_error_code != 0){ \
 *   const char *msg = yices_error_string(); \
 *   throwException(jenv, "java/lang/IllegalArgumentException", msg); \
 *   return -1; \
 * } \
 * 
 *INT_RETURN
 */
// above code might leak memory of error string

typedef jlong jjobjective_iterator;
#define OBJECTIVE_ITERATOR_ARG(num) STRUCT_ARG(msat_objective_iterator, num)
#define OBJECTIVE_ITERATOR_ARG_VOID(num) STRUCT_ARG_VOID(msat_objective_iterator, num)
#define OBJECTIVE_ITERATOR_RETURN STRUCT_RETURN_WITH_ENV

typedef jlong jjobjective;
#define OBJECTIVE_ARG(num) STRUCT_ARG(msat_objective, num)
#define OBJECTIVE_ARG_VOID(num) STRUCT_ARG_VOID(msat_objective, num)
#define OBJECTIVE_RETURN STRUCT_RETURN_WITH_ENV

typedef jlongArray jjobjectiveArray;
#define OBJECTIVE_POINTER_ARG(num) STRUCT_POINTER_ARG(msat_objective, num)
#define PUT_OBJECTIVE_POINTER_ARG(num) PUT_STRUCT_POINTER_ARG(num)

typedef jvoid jjfailureCode;

typedef jobject jjnamedtermswrapper;

// Abbreviations for common combinations of return and argument types
//
// Parameter explanation:
// func: the name of the Mathsat function (without msat_)
// func_escaped: the escaped variant of func
// jreturn: return type in Java world
// mreturn: return type of Mathsat C function
// margX: Java type of argument X
// jargX: Mathsat type of argument X

#define i_func1s(func, func_escaped, mreturn, marg1) \
  DEFINE_FUNC(int, func_escaped) WITH_ONE_ARG(long) \
  STRUCT_ARG(marg1, 1) \
  CALL1(mreturn, func) \
  INT_RETURN

#define make_term_constant(func, func_escaped) \
  DEFINE_FUNC(jterm, 1make_##func_escaped) WITH_ONE_ARG(jenv) \
  ENV_ARG(1) \
  CALL1(term_t, make_##func) \
  TERM_RETURN

#define get_yices_type(name) \
  DEFINE_FUNC(jtype, 1##name##_1type) WITHOUT_ARGS \
  CALL0(type_t, ##name##_type) \
  TYPE_RETURN

#define make_term_unary(name) \
  DEFINE_FUNC(jterm, 1make_1##name) WITH_TWO_ARGS(jenv, jterm) \
  ENV_ARG(1) \
  TERM_ARG(2) \
  CALL2(term_t, make_##name) \
  TERM_RETURN

#define make_term_binary(name) \
  DEFINE_FUNC(jterm, 1make_1##name) WITH_THREE_ARGS(jenv, jterm, jterm) \
  ENV_ARG(1) \
  TERM_ARG(2) \
  TERM_ARG(3) \
  CALL3(term_t, make_##name) \
  TERM_RETURN

#define yices_arith(name) \
  DEFINE_FUNC(jterm, 1arith_1##name##_1atom) WITH_ONE_ARG(jterm) \
  TERM_ARG(1) \
  CALL1(term_t, arith_##name##_atom) \
  TERM_RETURN

#define yices_arith2(name) \
  DEFINE_FUNC(jterm, 1arith_1##name##_1atom) WITH_TWO_ARGS(jterm, jterm) \
  TERM_ARG(1) \
  TERM_ARG(2) \
  CALL2(term_t, arith_##name##_atom) \
  TERM_RETURN

#define yices_type_is(name) \
  DEFINE_FUNC(jboolean, 1type_1is_1##name) WITH_ONE_ARG(jtype) \
  TYPE_ARG(1) \
  CALL1(type_t, type_is_##name) \
  BOOLEAN_RETURN

#define yices_term_is(name) \
  DEFINE_FUNC(jboolean, 1term_1is_1##name) WITH_ONE_ARG(jterm) \
  TERM_ARG(1) \
  CALL1(type_t, term_is_##name) \
  BOOLEAN_RETURN
  
