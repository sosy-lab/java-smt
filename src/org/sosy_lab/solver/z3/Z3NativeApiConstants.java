/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package org.sosy_lab.solver.z3;

import static org.sosy_lab.solver.z3.Z3NativeApi.get_app_decl;
import static org.sosy_lab.solver.z3.Z3NativeApi.get_decl_kind;
import static org.sosy_lab.solver.z3.Z3NativeApi.is_app;

/** This class contains many constants (enums) from Z3. */
class Z3NativeApiConstants {
  private Z3NativeApiConstants() {}

  /** returns, if the function of the expression is the given operation. */
  static boolean isOP(long z3context, long expr, int op) {
    if (!is_app(z3context, expr)) {
      return false;
    }

    long decl = get_app_decl(z3context, expr);
    return get_decl_kind(z3context, decl) == op;
  }

  // CONSTANT VALUES, TODO should we make enums?

  @SuppressWarnings("checkstyle:typename")
  enum Z3_LBOOL {
    Z3_L_FALSE(-1),
    Z3_L_UNDEF(0),
    Z3_L_TRUE(1);

    final int status;

    Z3_LBOOL(int status) {
      this.status = status;
    }
  }

  // Z3_ast_kind
  static final int Z3_NUMERAL_AST = 0;
  static final int Z3_APP_AST = 1;
  static final int Z3_VAR_AST = 2;
  static final int Z3_QUANTIFIER_AST = 3;
  static final int Z3_SORT_AST = 4;
  static final int Z3_FUNC_DECL_AST = 5;
  static final int Z3_UNKNOWN_AST = 1000;

  // Z3_sort_kind
  static final int Z3_UNINTERPRETED_SORT = 0;
  static final int Z3_BOOL_SORT = 1;
  static final int Z3_INT_SORT = 2;
  static final int Z3_REAL_SORT = 3;
  static final int Z3_BV_SORT = 4;
  static final int Z3_ARRAY_SORT = 5;
  static final int Z3_DATATYPE_SORT = 6;
  static final int Z3_RELATION_SORT = 7;
  static final int Z3_FINITE_DOMAIN_SORT = 8;
  static final int Z3_UNKNOWN_SORT = 1000;

  // Z3_symbol_kind
  static final int Z3_INT_SYMBOL = 0;
  static final int Z3_STRING_SYMBOL = 1;

  // Z3_decl_kind
  static final int Z3_OP_TRUE = 256;
  static final int Z3_OP_FALSE = 257;
  static final int Z3_OP_EQ = 258;
  static final int Z3_OP_DISTINCT = 259;
  static final int Z3_OP_ITE = 260;
  static final int Z3_OP_AND = 261;
  static final int Z3_OP_OR = 262;
  static final int Z3_OP_IFF = 263;
  static final int Z3_OP_XOR = 264;
  static final int Z3_OP_NOT = 265;
  static final int Z3_OP_IMPLIES = 266;
  static final int Z3_OP_OEQ = 267;

  static final int Z3_OP_ANUM = 512;
  static final int Z3_OP_AGNUM = 513;
  static final int Z3_OP_LE = 514;
  static final int Z3_OP_GE = 515;
  static final int Z3_OP_LT = 516;
  static final int Z3_OP_GT = 517;
  static final int Z3_OP_ADD = 518;
  static final int Z3_OP_SUB = 519;
  static final int Z3_OP_UMINUS = 520;
  static final int Z3_OP_MUL = 521;
  static final int Z3_OP_DIV = 522;
  static final int Z3_OP_IDIV = 523;
  static final int Z3_OP_REM = 524;
  static final int Z3_OP_MOD = 525;
  static final int Z3_OP_TO_REAL = 526;
  static final int Z3_OP_TO_INT = 527;
  static final int Z3_OP_IS_INT = 528;
  static final int Z3_OP_POWER = 529;

  static final int Z3_OP_STORE = 768;
  static final int Z3_OP_SELECT = 769;
  static final int Z3_OP_CONST_ARRAY = 770;
  static final int Z3_OP_ARRAY_MAP = 771;
  static final int Z3_OP_ARRAY_DEFAULT = 772;
  static final int Z3_OP_SET_UNION = 773;
  static final int Z3_OP_SET_INTERSECT = 774;
  static final int Z3_OP_SET_DIFFERENCE = 775;
  static final int Z3_OP_SET_COMPLEMENT = 776;
  static final int Z3_OP_SET_SUBSET = 777;
  static final int Z3_OP_AS_ARRAY = 778;

  static final int Z3_OP_BNUM = 1024;
  static final int Z3_OP_BIT1 = 1025;
  static final int Z3_OP_BIT0 = 1026;
  static final int Z3_OP_BNEG = 1027;
  static final int Z3_OP_BADD = 1028;
  static final int Z3_OP_BSUB = 1029;
  static final int Z3_OP_BMUL = 1030;
  static final int Z3_OP_BSDIV = 1031;
  static final int Z3_OP_BUDIV = 1032;
  static final int Z3_OP_BSREM = 1033;
  static final int Z3_OP_BUREM = 1034;
  static final int Z3_OP_BSMOD = 1035;
  static final int Z3_OP_BSDIV0 = 1036;
  static final int Z3_OP_BUDIV0 = 1037;
  static final int Z3_OP_BSREM0 = 1038;
  static final int Z3_OP_BUREM0 = 1039;
  static final int Z3_OP_BSMOD0 = 1040;
  static final int Z3_OP_ULEQ = 1041;
  static final int Z3_OP_SLEQ = 1042;
  static final int Z3_OP_UGEQ = 1043;
  static final int Z3_OP_SGEQ = 1044;
  static final int Z3_OP_ULT = 1045;
  static final int Z3_OP_SLT = 1046;
  static final int Z3_OP_UGT = 1047;
  static final int Z3_OP_SGT = 1048;
  static final int Z3_OP_BAND = 1049;

  static final int Z3_OP_BOR = 1050;
  static final int Z3_OP_BNOT = 1051;
  static final int Z3_OP_BXOR = 1052;
  static final int Z3_OP_BNAND = 1053;
  static final int Z3_OP_BNOR = 1054;
  static final int Z3_OP_BXNOR = 1055;
  static final int Z3_OP_CONCAT = 1056;
  static final int Z3_OP_SIGN_EXT = 1057;
  static final int Z3_OP_ZERO_EXT = 1058;
  static final int Z3_OP_EXTRACT = 1059;
  static final int Z3_OP_REPEAT = 1060;
  static final int Z3_OP_BREDOR = 1061;
  static final int Z3_OP_BREDAND = 1062;
  static final int Z3_OP_BCOMP = 1063;
  static final int Z3_OP_BSHL = 1064;
  static final int Z3_OP_BLSHR = 1065;
  static final int Z3_OP_BASHR = 1066;
  static final int Z3_OP_ROTATE_LEFT = 1067;
  static final int Z3_OP_ROTATE_RIGHT = 1068;
  static final int Z3_OP_EXT_ROTATE_LEFT = 1069;
  static final int Z3_OP_EXT_ROTATE_RIGHT = 1070;
  static final int Z3_OP_INT2BV = 1071;
  static final int Z3_OP_BV2INT = 1072;
  static final int Z3_OP_CARRY = 1073;
  static final int Z3_OP_XOR3 = 1074;

  static final int Z3_OP_PR_UNDEF = 1280;
  static final int Z3_OP_PR_TRUE = 1281;
  static final int Z3_OP_PR_ASSERTED = 1282;
  static final int Z3_OP_PR_GOAL = 1283;
  static final int Z3_OP_PR_MODUS_PONENS = 1284;
  static final int Z3_OP_PR_REFLEXIVITY = 1285;
  static final int Z3_OP_PR_SYMMETRY = 1286;
  static final int Z3_OP_PR_TRANSITIVITY = 1287;
  static final int Z3_OP_PR_TRANSITIVITY_STAR = 1288;
  static final int Z3_OP_PR_MONOTONICITY = 1289;
  static final int Z3_OP_PR_QUANT_INTRO = 1290;
  static final int Z3_OP_PR_DISTRIBUTIVITY = 1291;
  static final int Z3_OP_PR_AND_ELIM = 1292;
  static final int Z3_OP_PR_NOT_OR_ELIM = 1293;
  static final int Z3_OP_PR_REWRITE = 1294;
  static final int Z3_OP_PR_REWRITE_STAR = 1295;
  static final int Z3_OP_PR_PULL_QUANT = 1296;
  static final int Z3_OP_PR_PULL_QUANT_STAR = 1297;
  static final int Z3_OP_PR_PUSH_QUANT = 1298;
  static final int Z3_OP_PR_ELIM_UNUSED_VARS = 1299;

  static final int Z3_OP_PR_DER = 1300;
  static final int Z3_OP_PR_QUANT_INST = 1301;
  static final int Z3_OP_PR_HYPOTHESIS = 1302;
  static final int Z3_OP_PR_LEMMA = 1303;
  static final int Z3_OP_PR_UNIT_RESOLUTION = 1304;
  static final int Z3_OP_PR_IFF_TRUE = 1305;
  static final int Z3_OP_PR_IFF_FALSE = 1306;
  static final int Z3_OP_PR_COMMUTATIVITY = 1307;
  static final int Z3_OP_PR_DEF_AXIOM = 1308;
  static final int Z3_OP_PR_DEF_INTRO = 1309;
  static final int Z3_OP_PR_APPLY_DEF = 1310;
  static final int Z3_OP_PR_IFF_OEQ = 1311;
  static final int Z3_OP_PR_NNF_POS = 1312;
  static final int Z3_OP_PR_NNF_NEG = 1313;
  static final int Z3_OP_PR_NNF_STAR = 1314;
  static final int Z3_OP_PR_CNF_STAR = 1315;
  static final int Z3_OP_PR_SKOLEMIZE = 1316;
  static final int Z3_OP_PR_MODUS_PONENS_OEQ = 1317;
  static final int Z3_OP_PR_TH_LEMMA = 1318;
  static final int Z3_OP_PR_HYPER_RESOLVE = 1319;

  static final int Z3_OP_RA_STORE = 1536;
  static final int Z3_OP_RA_EMPTY = 1537;
  static final int Z3_OP_RA_IS_EMPTY = 1538;
  static final int Z3_OP_RA_JOIN = 1539;
  static final int Z3_OP_RA_UNION = 1540;
  static final int Z3_OP_RA_WIDEN = 1541;
  static final int Z3_OP_RA_PROJECT = 1542;
  static final int Z3_OP_RA_FILTER = 1543;
  static final int Z3_OP_RA_NEGATION_FILTER = 1544;
  static final int Z3_OP_RA_RENAME = 1545;
  static final int Z3_OP_RA_COMPLEMENT = 1546;
  static final int Z3_OP_RA_SELECT = 1547;
  static final int Z3_OP_RA_CLONE = 1548;
  static final int Z3_OP_FD_LT = 1549;

  static final int Z3_OP_LABEL = 1792;
  static final int Z3_OP_LABEL_LIT = 1793;

  static final int Z3_OP_DT_CONSTRUCTOR = 2048;
  static final int Z3_OP_DT_RECOGNISER = 2049;
  static final int Z3_OP_DT_ACCESSOR = 2050;
  static final int Z3_OP_UNINTERPRETED = 2051;

  // Z3_ast_print_mode
  static final int Z3_PRINT_SMTLIB_FULL = 0;
  static final int Z3_PRINT_LOW_LEVEL = 1;
  static final int Z3_PRINT_SMTLIB_COMPLIANT = 2;
  static final int Z3_PRINT_SMTLIB2_COMPLIANT = 3;
}
