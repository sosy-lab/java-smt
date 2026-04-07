/**
 * leansmt_wrapper.h
 *
 * C wrapper for lean-smt that hides Lean FFI complexity.
 * Exposes term-building API similar to other SMT solver bindings.
 */

#ifndef LEANSMT_WRAPPER_H
#define LEANSMT_WRAPPER_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Status codes */
#define LEANSMT_OK 0
#define LEANSMT_ERROR 1

/* Satisfiability results */
#define LEANSMT_SAT 0
#define LEANSMT_UNSAT 1
#define LEANSMT_UNKNOWN 2
#define LEANSMT_CHECK_ERROR 3

/* Solver kinds */
#define LEANSMT_SOLVER_CVC5 0
#define LEANSMT_SOLVER_Z3 1

/*=== Initialization ===*/

int leansmt_wrapper_init(void);
int leansmt_wrapper_is_initialized(void);
void leansmt_wrapper_cleanup(void);
const char* leansmt_wrapper_get_error(void);
int leansmt_wrapper_set_path_prefix(const char* dir);

/*=== Solver Management ===*/

uint64_t leansmt_wrapper_create_solver(int solver_kind);
int leansmt_wrapper_delete_solver(uint64_t handle);
int leansmt_wrapper_set_logic(uint64_t handle, const char* logic);

/*=== Term Creation - Constants ===*/

uint64_t leansmt_wrapper_mk_true(void);
uint64_t leansmt_wrapper_mk_false(void);
uint64_t leansmt_wrapper_mk_int_const(int64_t value);
uint64_t leansmt_wrapper_mk_real_const(int64_t num, int64_t den);
uint64_t leansmt_wrapper_mk_bv_const(uint32_t width, const char* value);

/*=== Generic/Indexed Operations ===*/

uint64_t leansmt_wrapper_mk_app1(const char* op, uint64_t term);
uint64_t leansmt_wrapper_mk_app2(const char* op, uint64_t lhs, uint64_t rhs);
uint64_t leansmt_wrapper_mk_extract(uint64_t term, uint32_t msb, uint32_t lsb);
uint64_t leansmt_wrapper_mk_indexed_app1(const char* op, uint32_t index, uint64_t term);
uint64_t leansmt_wrapper_mk_symbol(const char* symbol);
uint64_t leansmt_wrapper_mk_apply(uint64_t fn, uint64_t arg);
int leansmt_wrapper_get_term_kind(uint64_t term);
char* leansmt_wrapper_get_term_text(uint64_t term);
uint32_t leansmt_wrapper_get_term_num_children(uint64_t term);
uint64_t leansmt_wrapper_get_term_child(uint64_t term, uint32_t index);

/*=== Boolean Operations ===*/

uint64_t leansmt_wrapper_mk_not(uint64_t t);
uint64_t leansmt_wrapper_mk_and(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_or(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_xor(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_implies(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_iff(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_ite(uint64_t cond, uint64_t then_branch, uint64_t else_branch);

/*=== Comparison Operations ===*/

uint64_t leansmt_wrapper_mk_eq(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_distinct(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_lt(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_le(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_gt(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_ge(uint64_t t1, uint64_t t2);

/*=== Arithmetic Operations ===*/

uint64_t leansmt_wrapper_mk_add(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_sub(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_mul(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_div(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_mod(uint64_t t1, uint64_t t2);
uint64_t leansmt_wrapper_mk_neg(uint64_t t);

/*=== Solving ===*/

int leansmt_wrapper_assert(uint64_t solver, uint64_t term);
int leansmt_wrapper_declare_fun(
    uint64_t solver, const char* name, const char* arg_sorts, const char* return_sort);
int leansmt_wrapper_check_sat(uint64_t solver);
char* leansmt_wrapper_get_model(uint64_t solver);
char* leansmt_wrapper_get_value(uint64_t solver, uint64_t term);
void leansmt_wrapper_free_string(char* value);

#ifdef __cplusplus
}
#endif

#endif /* LEANSMT_WRAPPER_H */
