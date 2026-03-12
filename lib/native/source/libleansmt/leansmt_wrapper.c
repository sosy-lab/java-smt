/**
 * leansmt_wrapper.c
 *
 * C wrapper implementation that handles Lean FFI complexity.
 */

#define _GNU_SOURCE

#include "leansmt_wrapper.h"
#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <unistd.h>
#include <dlfcn.h>

/* Lean runtime functions */
extern void lean_initialize_runtime_module(void);
extern void lean_init_task_manager(void);
extern void lean_finalize_task_manager(void);
extern void lean_io_mark_end_initialization(void);

/* Lean module initializer.
 * Depending on Lean packaging/module naming, the generated symbol can use
 * either a flat module name (initialize_SmtJNI) or a namespaced one
 * (initialize_smt_SmtJNI). Keep both as weak references and resolve at runtime.
 */
extern lean_object* initialize_SmtJNI(uint8_t builtin) __attribute__((weak));
extern lean_object* initialize_smt_SmtJNI(uint8_t builtin) __attribute__((weak));

/* Lean-smt exported functions */
extern lean_object* leansmt_init(void);
extern lean_object* leansmt_get_error(void);
extern lean_object* leansmt_cleanup(void);
extern lean_object* leansmt_create_solver(uint8_t kind);
extern lean_object* leansmt_delete_solver(uint64_t handle);
extern lean_object* leansmt_set_logic(uint64_t handle, lean_object* logic);
extern lean_object* leansmt_mk_bool_var(uint64_t solver, lean_object* name);
extern lean_object* leansmt_mk_int_var(uint64_t solver, lean_object* name);
extern lean_object* leansmt_mk_real_var(uint64_t solver, lean_object* name);
extern lean_object* leansmt_mk_bv_var(uint64_t solver, lean_object* name, uint32_t width);
extern lean_object* leansmt_mk_int_const(lean_object* value);
extern lean_object* leansmt_mk_real_const(lean_object* num, lean_object* den);
extern lean_object* leansmt_mk_bv_const(uint32_t width, lean_object* value);
extern lean_object* leansmt_mk_true(void);
extern lean_object* leansmt_mk_false(void);
extern lean_object* leansmt_mk_app1(lean_object* op, uint64_t term);
extern lean_object* leansmt_mk_app2(lean_object* op, uint64_t lhs, uint64_t rhs);
extern lean_object* leansmt_mk_extract(uint64_t term, uint32_t msb, uint32_t lsb);
extern lean_object* leansmt_mk_indexed_app1(lean_object* op, uint32_t index, uint64_t term);
extern lean_object* leansmt_mk_not(uint64_t t);
extern lean_object* leansmt_mk_and(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_or(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_xor(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_implies(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_iff(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_ite(uint64_t cond, uint64_t then_b, uint64_t else_b);
extern lean_object* leansmt_mk_eq(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_distinct(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_lt(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_le(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_gt(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_ge(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_add(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_sub(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_mul(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_div(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_mod(uint64_t t1, uint64_t t2);
extern lean_object* leansmt_mk_neg(uint64_t t);
extern lean_object* leansmt_assert(uint64_t solver, uint64_t term);
extern lean_object* leansmt_check_sat(uint64_t solver);
extern lean_object* leansmt_get_model(uint64_t solver);
extern lean_object* leansmt_get_proof(uint64_t solver);
extern lean_object* leansmt_check_sat_string(lean_object* query);

/* Internal state */
static int g_initialized = 0;
static char g_error_buffer[4096] = {0};

typedef lean_object* (*leansmt_module_initializer_t)(uint8_t builtin);

/*=== Helper functions ===*/

static int file_is_executable(const char* path) {
    return path != NULL && access(path, X_OK) == 0;
}

static int path_contains_entry(const char* path_value, const char* entry) {
    if (path_value == NULL || entry == NULL || entry[0] == '\0') {
        return 0;
    }

    const size_t entry_len = strlen(entry);
    const char* part = path_value;
    while (*part != '\0') {
        const char* sep = strchr(part, ':');
        size_t len = (sep == NULL) ? strlen(part) : (size_t)(sep - part);
        if (len == entry_len && strncmp(part, entry, entry_len) == 0) {
            return 1;
        }
        if (sep == NULL) {
            break;
        }
        part = sep + 1;
    }
    return 0;
}

static void prepend_to_path(const char* dir) {
    if (dir == NULL || dir[0] == '\0') {
        return;
    }

    const char* old_path = getenv("PATH");
    if (path_contains_entry(old_path, dir)) {
        return;
    }

    const size_t dir_len = strlen(dir);
    const size_t old_len = (old_path == NULL) ? 0 : strlen(old_path);
    const size_t total = dir_len + 1 + old_len + 1;
    char* new_path = (char*)malloc(total);
    if (new_path == NULL) {
        return;
    }

    if (old_len > 0) {
        snprintf(new_path, total, "%s:%s", dir, old_path);
    } else {
        snprintf(new_path, total, "%s", dir);
    }
    setenv("PATH", new_path, 1);
    free(new_path);
}

int leansmt_wrapper_set_path_prefix(const char* dir) {
    if (dir == NULL || dir[0] == '\0') {
        return LEANSMT_ERROR;
    }
    prepend_to_path(dir);
    return LEANSMT_OK;
}

static void configure_embedded_cvc5_path(void) {
    Dl_info info;
    if (dladdr((void*)&leansmt_wrapper_init, &info) == 0 || info.dli_fname == NULL) {
        return;
    }

    char lib_dir[PATH_MAX];
    strncpy(lib_dir, info.dli_fname, sizeof(lib_dir) - 1);
    lib_dir[sizeof(lib_dir) - 1] = '\0';
    char* slash = strrchr(lib_dir, '/');
    if (slash == NULL) {
        return;
    }
    *slash = '\0';

    const char* candidates[] = {
        "cvc5",
        "leansmt-runtime/cvc5",
        "leansmt-runtime/bin/cvc5",
    };

    for (size_t i = 0; i < sizeof(candidates) / sizeof(candidates[0]); i++) {
        char solver_path[PATH_MAX];
        int written =
            snprintf(solver_path, sizeof(solver_path), "%s/%s", lib_dir, candidates[i]);
        if (written <= 0 || (size_t)written >= sizeof(solver_path)) {
            continue;
        }
        if (!file_is_executable(solver_path)) {
            continue;
        }

        char solver_dir[PATH_MAX];
        strncpy(solver_dir, solver_path, sizeof(solver_dir) - 1);
        solver_dir[sizeof(solver_dir) - 1] = '\0';
        char* solver_slash = strrchr(solver_dir, '/');
        if (solver_slash == NULL) {
            continue;
        }
        *solver_slash = '\0';
        prepend_to_path(solver_dir);
        return;
    }
}

static int32_t extract_io_uint32(lean_object* result) {
    if (lean_obj_tag(result) == 0) {
        lean_object* value = lean_ctor_get(result, 0);
        uint32_t ret = lean_unbox_uint32(value);
        lean_dec_ref(result);
        return (int32_t)ret;
    }
    lean_dec_ref(result);
    return -1;
}

static uint64_t extract_io_uint64(lean_object* result) {
    if (lean_obj_tag(result) == 0) {
        lean_object* value = lean_ctor_get(result, 0);
        uint64_t ret = lean_unbox_uint64(value);
        lean_dec_ref(result);
        return ret;
    }
    lean_dec_ref(result);
    return 0;
}

static uint8_t extract_io_uint8(lean_object* result) {
    if (lean_obj_tag(result) == 0) {
        lean_object* value = lean_ctor_get(result, 0);
        uint8_t ret = lean_unbox(value);
        lean_dec_ref(result);
        return ret;
    }
    lean_dec_ref(result);
    return 255;
}

static char* extract_io_string(lean_object* result) {
    if (lean_obj_tag(result) == 0) {
        lean_object* value = lean_ctor_get(result, 0);
        if (lean_is_scalar(value)) {
            lean_dec_ref(result);
            return strdup("");
        }
        const char* str = lean_string_cstr(value);
        char* copy = strdup(str);
        lean_dec_ref(result);
        return copy;
    }
    lean_dec_ref(result);
    return NULL;
}

static leansmt_module_initializer_t resolve_smtjni_initializer(void) {
    if (initialize_smt_SmtJNI != NULL) {
        return initialize_smt_SmtJNI;
    }
    if (initialize_SmtJNI != NULL) {
        return initialize_SmtJNI;
    }
    return NULL;
}

/*=== Initialization ===*/

int leansmt_wrapper_init(void) {
    if (g_initialized) {
        return LEANSMT_OK;
    }

    configure_embedded_cvc5_path();

    lean_initialize_runtime_module();
    lean_init_task_manager();

    leansmt_module_initializer_t init_smtjni = resolve_smtjni_initializer();
    if (init_smtjni == NULL) {
        snprintf(g_error_buffer, sizeof(g_error_buffer),
                 "Failed to locate SmtJNI module initializer symbol");
        return LEANSMT_ERROR;
    }

    lean_object* init_res = init_smtjni(1);
    if (lean_io_result_is_error(init_res)) {
        snprintf(g_error_buffer, sizeof(g_error_buffer),
                 "Failed to initialize SmtJNI module");
        lean_dec_ref(init_res);
        return LEANSMT_ERROR;
    }
    lean_dec_ref(init_res);

    lean_io_mark_end_initialization();

    lean_object* result = leansmt_init();
    int32_t ret = extract_io_uint32(result);
    if (ret != 0) {
        snprintf(g_error_buffer, sizeof(g_error_buffer),
                 "leansmt_init returned error code: %d", ret);
        return LEANSMT_ERROR;
    }

    g_initialized = 1;
    return LEANSMT_OK;
}

int leansmt_wrapper_is_initialized(void) {
    return g_initialized;
}

void leansmt_wrapper_cleanup(void) {
    if (!g_initialized) return;
    lean_object* result = leansmt_cleanup();
    lean_dec_ref(result);
    lean_finalize_task_manager();
    g_initialized = 0;
    g_error_buffer[0] = '\0';
}

const char* leansmt_wrapper_get_error(void) {
    if (!g_initialized) return "Library not initialized";
    lean_object* result = leansmt_get_error();
    char* err = extract_io_string(result);
    if (err && strlen(err) > 0) {
        strncpy(g_error_buffer, err, sizeof(g_error_buffer) - 1);
        free(err);
        return g_error_buffer;
    }
    if (err) free(err);
    if (g_error_buffer[0] != '\0') return g_error_buffer;
    return NULL;
}

/*=== Solver Management ===*/

uint64_t leansmt_wrapper_create_solver(int solver_kind) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_create_solver((uint8_t)solver_kind));
}

int leansmt_wrapper_delete_solver(uint64_t handle) {
    if (!g_initialized) return LEANSMT_ERROR;
    int32_t ret = extract_io_uint32(leansmt_delete_solver(handle));
    return (ret == 0) ? LEANSMT_OK : LEANSMT_ERROR;
}

int leansmt_wrapper_set_logic(uint64_t handle, const char* logic) {
    if (!g_initialized || !logic) return LEANSMT_ERROR;
    lean_object* lean_logic = lean_mk_string(logic);
    int32_t ret = extract_io_uint32(leansmt_set_logic(handle, lean_logic));
    return (ret == 0) ? LEANSMT_OK : LEANSMT_ERROR;
}

/*=== Term Creation - Variables ===*/

uint64_t leansmt_wrapper_mk_bool_var(uint64_t solver, const char* name) {
    if (!g_initialized || !name) return 0;
    lean_object* lean_name = lean_mk_string(name);
    return extract_io_uint64(leansmt_mk_bool_var(solver, lean_name));
}

uint64_t leansmt_wrapper_mk_int_var(uint64_t solver, const char* name) {
    if (!g_initialized || !name) return 0;
    lean_object* lean_name = lean_mk_string(name);
    return extract_io_uint64(leansmt_mk_int_var(solver, lean_name));
}

uint64_t leansmt_wrapper_mk_real_var(uint64_t solver, const char* name) {
    if (!g_initialized || !name) return 0;
    lean_object* lean_name = lean_mk_string(name);
    return extract_io_uint64(leansmt_mk_real_var(solver, lean_name));
}

uint64_t leansmt_wrapper_mk_bv_var(uint64_t solver, const char* name, uint32_t width) {
    if (!g_initialized || !name || width == 0) return 0;
    lean_object* lean_name = lean_mk_string(name);
    return extract_io_uint64(leansmt_mk_bv_var(solver, lean_name, width));
}

/*=== Term Creation - Constants ===*/

uint64_t leansmt_wrapper_mk_true(void) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_true());
}

uint64_t leansmt_wrapper_mk_false(void) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_false());
}

uint64_t leansmt_wrapper_mk_int_const(int64_t value) {
    if (!g_initialized) return 0;
    lean_object* lean_val = lean_int_to_int(value);
    return extract_io_uint64(leansmt_mk_int_const(lean_val));
}

uint64_t leansmt_wrapper_mk_real_const(int64_t num, int64_t den) {
    if (!g_initialized) return 0;
    lean_object* lean_num = lean_int_to_int(num);
    lean_object* lean_den = lean_int_to_int(den);
    return extract_io_uint64(leansmt_mk_real_const(lean_num, lean_den));
}

uint64_t leansmt_wrapper_mk_bv_const(uint32_t width, const char* value) {
    if (!g_initialized || width == 0 || value == NULL) return 0;
    lean_object* lean_value = lean_mk_string(value);
    return extract_io_uint64(leansmt_mk_bv_const(width, lean_value));
}

/*=== Generic/Indexed Operations ===*/

uint64_t leansmt_wrapper_mk_app1(const char* op, uint64_t term) {
    if (!g_initialized || op == NULL) return 0;
    lean_object* lean_op = lean_mk_string(op);
    return extract_io_uint64(leansmt_mk_app1(lean_op, term));
}

uint64_t leansmt_wrapper_mk_app2(const char* op, uint64_t lhs, uint64_t rhs) {
    if (!g_initialized || op == NULL) return 0;
    lean_object* lean_op = lean_mk_string(op);
    return extract_io_uint64(leansmt_mk_app2(lean_op, lhs, rhs));
}

uint64_t leansmt_wrapper_mk_extract(uint64_t term, uint32_t msb, uint32_t lsb) {
    if (!g_initialized || msb < lsb) return 0;
    return extract_io_uint64(leansmt_mk_extract(term, msb, lsb));
}

uint64_t leansmt_wrapper_mk_indexed_app1(const char* op, uint32_t index, uint64_t term) {
    if (!g_initialized || op == NULL) return 0;
    lean_object* lean_op = lean_mk_string(op);
    return extract_io_uint64(leansmt_mk_indexed_app1(lean_op, index, term));
}

/*=== Boolean Operations ===*/

uint64_t leansmt_wrapper_mk_not(uint64_t t) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_not(t));
}

uint64_t leansmt_wrapper_mk_and(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_and(t1, t2));
}

uint64_t leansmt_wrapper_mk_or(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_or(t1, t2));
}

uint64_t leansmt_wrapper_mk_xor(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_xor(t1, t2));
}

uint64_t leansmt_wrapper_mk_implies(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_implies(t1, t2));
}

uint64_t leansmt_wrapper_mk_iff(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_iff(t1, t2));
}

uint64_t leansmt_wrapper_mk_ite(uint64_t cond, uint64_t then_branch, uint64_t else_branch) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_ite(cond, then_branch, else_branch));
}

/*=== Comparison Operations ===*/

uint64_t leansmt_wrapper_mk_eq(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_eq(t1, t2));
}

uint64_t leansmt_wrapper_mk_distinct(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_distinct(t1, t2));
}

uint64_t leansmt_wrapper_mk_lt(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_lt(t1, t2));
}

uint64_t leansmt_wrapper_mk_le(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_le(t1, t2));
}

uint64_t leansmt_wrapper_mk_gt(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_gt(t1, t2));
}

uint64_t leansmt_wrapper_mk_ge(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_ge(t1, t2));
}

/*=== Arithmetic Operations ===*/

uint64_t leansmt_wrapper_mk_add(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_add(t1, t2));
}

uint64_t leansmt_wrapper_mk_sub(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_sub(t1, t2));
}

uint64_t leansmt_wrapper_mk_mul(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_mul(t1, t2));
}

uint64_t leansmt_wrapper_mk_div(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_div(t1, t2));
}

uint64_t leansmt_wrapper_mk_mod(uint64_t t1, uint64_t t2) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_mod(t1, t2));
}

uint64_t leansmt_wrapper_mk_neg(uint64_t t) {
    if (!g_initialized) return 0;
    return extract_io_uint64(leansmt_mk_neg(t));
}

/*=== Solving ===*/

int leansmt_wrapper_assert(uint64_t solver, uint64_t term) {
    if (!g_initialized) return LEANSMT_ERROR;
    int32_t ret = extract_io_uint32(leansmt_assert(solver, term));
    return (ret == 0) ? LEANSMT_OK : LEANSMT_ERROR;
}

int leansmt_wrapper_check_sat(uint64_t solver) {
    if (!g_initialized) return LEANSMT_CHECK_ERROR;
    uint8_t result = extract_io_uint8(leansmt_check_sat(solver));
    switch (result) {
        case 0:
            return LEANSMT_SAT;
        case 1:
            return LEANSMT_UNSAT;
        case 2:
            return LEANSMT_UNKNOWN;
        default:
            return LEANSMT_CHECK_ERROR;
    }
}

char* leansmt_wrapper_get_model(uint64_t solver) {
    if (!g_initialized) return NULL;
    return extract_io_string(leansmt_get_model(solver));
}

char* leansmt_wrapper_get_proof(uint64_t solver) {
    if (!g_initialized) return NULL;
    return extract_io_string(leansmt_get_proof(solver));
}

void leansmt_wrapper_free_string(char* value) {
    if (value != NULL) {
        free(value);
    }
}

/*=== Legacy/Convenience ===*/

int leansmt_wrapper_check_sat_string(const char* query) {
    if (!g_initialized || query == NULL) return LEANSMT_CHECK_ERROR;
    lean_object* lean_query = lean_mk_string(query);
    uint8_t result = extract_io_uint8(leansmt_check_sat_string(lean_query));
    switch (result) {
        case 0:
            return LEANSMT_SAT;
        case 1:
            return LEANSMT_UNSAT;
        case 2:
            return LEANSMT_UNKNOWN;
        default:
            return LEANSMT_CHECK_ERROR;
    }
}
