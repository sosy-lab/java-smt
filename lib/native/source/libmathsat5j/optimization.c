#include "includes/defines.h"

void throwException(JNIEnv *env, const char *name, const char *msg);

DEFINE_FUNC(jenv, 1create_1opt_1env) WITH_ONE_ARG(jconf)
CONF_ARG(1)
CALL1(msat_env, create_opt_env)
ENV_RETURN

/*
 * msat_env msat_create_shared_opt_env(msat_config cfg, msat_env sibling);
 */
DEFINE_FUNC(jenv, 1create_1shared_1opt_1env) WITH_TWO_ARGS(jconf, jenv)
CONF_ARG(1)
ENV_ARG(2)
CALL2(msat_env, create_shared_opt_env)
ENV_RETURN

#define make_minmax(func, func_escaped) \
  DEFINE_FUNC(jobjective, 1make_##func_escaped) WITH_TWO_ARGS(jenv, jterm) \
  ENV_ARG(1) \
  TERM_ARG(2) \
  CALL2(msat_objective, make_##func) \
  STRUCT_RETURN_WITH_ENV

#define make_minmax_array(func, func_escaped) \
  DEFINE_FUNC(jobjective, 1make_##func_escaped) WITH_THREE_ARGS(jenv, int, jtermArray) \
  ENV_ARG(1) \
  SIMPLE_ARG(size_t, 2) \
  TERM_ARRAY_ARG(3) \
  CALL3(msat_objective, make_##func) \
  FREE_TERM_ARRAY_ARG(3)\
  STRUCT_RETURN_WITH_ENV

make_minmax(minimize, 1minimize)
make_minmax(minimize_signed, 1minimize_1signed)
make_minmax(maximize, 1maximize)
make_minmax(maximize_signed, 1maximize_1signed)

make_minmax_array(minmax, 1minmax)
make_minmax_array(minmax_signed, 1minmax_1signed)
make_minmax_array(maxmin, 1maxmin)
make_minmax_array(maxmin_signed, 1maxmin_1signed)

DEFINE_FUNC(jfailureCode, 1assert_1soft_1formula) WITH_FOUR_ARGS(jenv, jterm, jterm, string)
ENV_ARG_VOID(1)
TERM_ARG_VOID(2)
TERM_ARG_VOID(3)
STRING_ARG(4)
CALL4(int, assert_soft_formula)
FREE_STRING_ARG(4)
FAILURE_CODE_RETURN

DEFINE_FUNC(jobjective_iterator, 1create_1objective_1iterator) WITH_ONE_ARG(jenv)
ENV_ARG(1)
CALL1(msat_objective_iterator, create_objective_iterator)
OBJECTIVE_ITERATOR_RETURN

DEFINE_FUNC(int, 1objective_1iterator_1has_1next) WITH_ONE_ARG(jobjective_iterator)
OBJECTIVE_ITERATOR_ARG(1)
CALL1(int, objective_iterator_has_next)
INT_RETURN

DEFINE_FUNC(int, 1objective_1iterator_1next) WITH_TWO_ARGS(jobjective_iterator, jobjectiveArray)
OBJECTIVE_ITERATOR_ARG(1)
OBJECTIVE_POINTER_ARG(2)
CALL2(int, objective_iterator_next)
PUT_OBJECTIVE_POINTER_ARG(2)
INT_RETURN

DEFINE_FUNC(void, 1destroy_1objective_1iterator) WITH_ONE_ARG(jobjective_iterator)
OBJECTIVE_ITERATOR_ARG_VOID(1)
VOID_CALL1(destroy_objective_iterator)

DEFINE_FUNC(int, 1objective_1result) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG(1)
OBJECTIVE_ARG(2)
CALL2(msat_result, objective_result)
INT_RETURN

DEFINE_FUNC(jterm, 1objective_1get_1term) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG(1)
OBJECTIVE_ARG(2)
CALL2(msat_term, objective_get_term)
TERM_RETURN

DEFINE_FUNC(int, 1objective_1get_1type) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG(1)
OBJECTIVE_ARG(2)
CALL2(msat_objective_type, objective_get_type)
INT_RETURN

DEFINE_FUNC(jfailureCode, 1load_1objective_1model) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG_VOID(1)
OBJECTIVE_ARG_VOID(2)
CALL2(int, load_objective_model)
FAILURE_CODE_RETURN

DEFINE_FUNC(string, 1objective_1get_1search_1stats) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG(1)
OBJECTIVE_ARG(2)
CALL2(const char *, objective_get_search_stats)
CONST_STRING_RETURN

DEFINE_FUNC(int, 1objective_1value_1is_1unbounded) WITH_THREE_ARGS(jenv, jobjective, int)
ENV_ARG(1)
OBJECTIVE_ARG(2)
SIMPLE_ARG(int, 3)
CALL3(int, objective_value_is_unbounded)
INT_RETURN

DEFINE_FUNC(int, 1objective_1value_1is_1plus_1inf) WITH_THREE_ARGS(jenv, jobjective, int)
ENV_ARG(1)
OBJECTIVE_ARG(2)
SIMPLE_ARG(int, 3)
CALL3(int, objective_value_is_plus_inf)
INT_RETURN

DEFINE_FUNC(int, 1objective_1value_1is_1minus_1inf) WITH_THREE_ARGS(jenv, jobjective, int)
ENV_ARG(1)
OBJECTIVE_ARG(2)
SIMPLE_ARG(int, 3)
CALL3(int, objective_value_is_minus_inf)
INT_RETURN

DEFINE_FUNC(int, 1objective_1value_1is_1strict) WITH_THREE_ARGS(jenv, jobjective, int)
ENV_ARG(1)
OBJECTIVE_ARG(2)
SIMPLE_ARG(int, 3)
CALL3(int, objective_value_is_strict)
INT_RETURN

DEFINE_FUNC(jterm, 1objective_1value_1term) WITH_FIVE_ARGS(jenv, jobjective, int, jterm, jterm)
ENV_ARG(1)
OBJECTIVE_ARG(2)
SIMPLE_ARG(int, 3)
ERROR_TERM_ARG(4)
ERROR_TERM_ARG(5)
CALL5(msat_term, objective_value_term)
TERM_RETURN

DEFINE_FUNC(jfailureCode, 1assert_1objective) WITH_TWO_ARGS(jenv, jobjective)
ENV_ARG_VOID(1)
OBJECTIVE_ARG_VOID(2)
CALL2(int, assert_objective)
FAILURE_CODE_RETURN
