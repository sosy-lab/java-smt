/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016, Antti Hyvarinen
                          2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef OPENSMT_C_H
#define OPENSMT_C_H

#ifdef __cplusplus
extern "C" {
#endif

#include "Global.h"
//
// Datatypes
//
typedef struct osmt_expr { unsigned x; } osmt_expr;
typedef struct osmt_context { void *c; } osmt_context;
typedef enum { l_false=-1, l_undef, l_true } osmt_result;
typedef enum
{
    qf_uf         // Uninterpreted Functions
  , qf_bv         // BitVectors
  , qf_rdl        // Real difference logics
  , qf_idl        // Integer difference logics
  , qf_lra        // Real linear arithmetic
  , qf_lia        // Integer linear arithmetic
  , qf_ufidl      // UF + IDL
  , qf_uflra      // UF + LRA
  , qf_bool       // Only booleans
  , qf_ct         // Cost
} osmt_logic;
//
// Communication APIs
//
void             osmt_set_verbosity             ( osmt_context, int );
char *           osmt_version                   ( );
void             osmt_print_expr                ( osmt_context, osmt_expr );
osmt_context     osmt_mk_context                ( osmt_logic );
void             osmt_del_context               ( osmt_context );
void             osmt_reset                     ( osmt_context );
void             osmt_push                      ( osmt_context, osmt_expr );
void             osmt_pop                       ( osmt_context );
osmt_result      osmt_check                     ( osmt_context );
unsigned         osmt_conflicts                 ( osmt_context );
unsigned         osmt_decisions                 ( osmt_context );
osmt_expr        osmt_get_value                 ( osmt_context, osmt_expr );
//void             osmt_get_num                   ( osmt_expr n, mpz_t val );
osmt_result      osmt_get_bool                  ( osmt_context c, osmt_expr p );
void             osmt_polarity                  ( osmt_context c, osmt_expr a, int pos );


void             osmt_get_model                 ( osmt_context, const char * );
//void             osmt_print_proof               ( osmt_context, const char * );
//void             osmt_print_interpolant         ( osmt_context, const char * );

void             osmt_dump_assertions_to_file   ( osmt_context, const char * );

//
// Formula construction APIs
//
osmt_expr     osmt_mk_true                   ( osmt_context );
osmt_expr     osmt_mk_false                  ( osmt_context );
osmt_expr     osmt_mk_bool_var               ( osmt_context, const char * );
osmt_expr     osmt_mk_real_var               ( osmt_context, const char * );
osmt_expr     osmt_mk_or                     ( osmt_context, osmt_expr *, unsigned );
osmt_expr     osmt_mk_and                    ( osmt_context, osmt_expr *, unsigned );
osmt_expr     osmt_mk_eq                     ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_ite                    ( osmt_context, osmt_expr, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_not                    ( osmt_context, osmt_expr );
osmt_expr     osmt_mk_impl                   ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_xor                    ( osmt_context, osmt_expr, osmt_expr );

osmt_expr     osmt_mk_num_from_string        ( osmt_context, const char * );
osmt_expr     osmt_mk_num_from_frac          ( osmt_context, const int nom, const int den);
osmt_expr     osmt_mk_num_from_num           ( osmt_context, const int num );
osmt_expr     osmt_mk_plus                   ( osmt_context, osmt_expr *, unsigned );
osmt_expr     osmt_mk_minus                  ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_times                  ( osmt_context, osmt_expr *, unsigned );
osmt_expr     osmt_mk_lt                     ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_leq                    ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_gt                     ( osmt_context, osmt_expr, osmt_expr );
osmt_expr     osmt_mk_geq                    ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_int_var                ( osmt_context, const char * );
//osmt_expr     osmt_mk_bv_var                 ( osmt_context, const char *, unsigned );
//osmt_expr     osmt_mk_cost_var               ( osmt_context, const char * );
//osmt_expr     osmt_mk_diseq                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_num_from_mpz           ( osmt_context, const mpz_t );
//osmt_expr     osmt_mk_num_from_mpq           ( osmt_context, const mpq_t );

//osmt_expr     osmt_mk_bv_constant            ( osmt_context, unsigned, unsigned long );
//osmt_expr     osmt_mk_bv_constant_from_string( osmt_context, unsigned, const char * );
//osmt_expr     osmt_mk_bv_add                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_sub                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_mul                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_minus               ( osmt_context, osmt_expr );
//osmt_expr     osmt_mk_bv_concat              ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_and                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_or                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_xor                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_not                 ( osmt_context, osmt_expr );
//osmt_expr     osmt_mk_bv_extract             ( osmt_context, unsigned, unsigned, osmt_expr );
//osmt_expr     osmt_mk_bv_sign_extend         ( osmt_context, osmt_expr, unsigned );
//osmt_expr     osmt_mk_bv_shift_left0         ( osmt_context, osmt_expr, unsigned );
//osmt_expr     osmt_mk_bv_shift_left1         ( osmt_context, osmt_expr, unsigned );
//osmt_expr     osmt_mk_bv_shift_right0        ( osmt_context, osmt_expr, unsigned );
//osmt_expr     osmt_mk_bv_shift_right1        ( osmt_context, osmt_expr, unsigned );
//osmt_expr     osmt_mk_bv_lt                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_le                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_gt                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_ge                  ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_slt                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_sle                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_sgt                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_bv_sge                 ( osmt_context, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_ct_incur               ( osmt_context, osmt_expr, osmt_expr, osmt_expr );
//osmt_expr     osmt_mk_ct_bound               ( osmt_context, osmt_expr, osmt_expr );

#ifdef __cplusplus
}
#endif

#endif
