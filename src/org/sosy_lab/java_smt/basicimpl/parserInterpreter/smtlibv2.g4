/**
 * SMT-LIB (v2.6) grammar
 *
 * Grammar is based on the following specification:
 * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 **/

/*
 * SPDX-FileCopyrightText: 2017 Julian Thome <julian.thome.de@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

grammar smtlibv2;


// Lexer Rules Start


Comment
    : Semicolon ~[\r\n]* -> skip
    ;


ParOpen
    : '('
    ;

ParClose
    : ')'
    ;

Semicolon
    : ';'
    ;

String
    : '"' (PrintableCharNoDquote | WhiteSpaceChar)+ '"'
    ;

QuotedSymbol:
    '|' (PrintableCharNoBackslash | WhiteSpaceChar)+ '|'
    ;


// Predefined Symbols

PS_Not
    : 'not'
    ;
PS_Bool
    : 'Bool'
    ;
PS_ContinuedExecution
    : 'continued-execution'
    ;
PS_Error
    : 'error'
    ;
PS_False
    : 'false'
    ;
PS_ImmediateExit
    : 'immediate-exit'
    ;
PS_Incomplete
    : 'incomplete'
    ;
PS_Logic
    : 'logic'
    ;
PS_Memout
    : 'memout'
    ;
PS_Sat
    : 'sat'
    ;
PS_Success
    : 'success'
    ;
PS_Theory
    : 'theory'
    ;
PS_True
    : 'true'
    ;
PS_Unknown
    : 'unknown'
    ;
PS_Unsupported
    : 'unsupported'
    ;
PS_Unsat
    : 'unsat'
    ;

// RESERVED Words

// Command names


CMD_Assert
    : 'assert'
    ;
CMD_CheckSat
    : 'check-sat'
    ;
CMD_CheckSatAssuming
    : 'check-sat-assuming'
    ;
CMD_DeclareConst
    : 'declare-const'
    ;
CMD_DeclareDatatype
    : 'declare-datatype'
    ;
CMD_DeclareDatatypes
    : 'declare-datatypes'
    ;
CMD_DeclareFun
    : 'declare-fun'
    ;
CMD_DeclareSort
    : 'declare-sort'
    ;
CMD_DefineFun
    : 'define-fun'
    ;
CMD_DefineFunRec
    : 'define-fun-rec'
    ;
CMD_DefineFunsRec
    : 'define-funs-rec'
    ;
CMD_DefineSort
    : 'define-sort'
    ;
CMD_Echo
    : 'echo'
    ;
CMD_Exit
    : 'exit'
    ;
CMD_GetAssertions
    : 'get-assertions'
    ;
CMD_GetAssignment
    : 'get-assignment'
    ;
CMD_GetInfo
    : 'get-info'
    ;
CMD_GetModel
    : 'get-model'
    ;
CMD_GetOption
    : 'get-option'
    ;
CMD_GetProof
    : 'get-proof'
    ;
CMD_GetUnsatAssumptions
    : 'get-unsat-assumptions'
    ;
CMD_GetUnsatCore
    : 'get-unsat-core'
    ;
CMD_GetValue
    : 'get-value'
    ;
CMD_Pop
    : 'pop'
    ;
CMD_Push
    : 'push'
    ;
CMD_Reset
    : 'reset'
    ;
CMD_ResetAssertions
    : 'reset-assertions'
    ;
CMD_SetInfo
    : 'set-info'
    ;
CMD_SetLogic
    : 'set-logic'
    ;
CMD_SetOption
    : 'set-option'
    ;




// General reserved words

GRW_Exclamation
    : '!'
    ;
GRW_Underscore
    : '_'
    ;
GRW_As
    : 'as'
    ;
GRW_Binary
    : 'BINARY'
    ;
GRW_Decimal
    : 'DECIMAL'
    ;
GRW_Exists
    : 'exists'
    ;
GRW_Hexadecimal
    : 'HEXADECIMAL'
    ;
GRW_Forall
    : 'forall'
    ;
GRW_Let
    : 'let'
    ;
GRW_Match
    : 'match'
    ;
GRW_Numeral
    : 'NUMERAL'
    ;
GRW_Par
    : 'par'
    ;
GRW_String
    : 'string'
    ;

Numeral
    : '0'
    | [1-9] Digit*
    ;

Binary
    : '#b' BinaryDigit+
    ;

Real //The official website declares reals in their theories which is just decimal.
    :Decimal
    ;

HexDecimal
    : '#x' HexDigit+
    ;

Decimal
    : Numeral '.' '0'* Numeral
    ;

RoundingModes //needed for floating point operations
    : 'RNE'
    | 'RNA'
    | 'RTP'
    | 'RTN'
    | 'RTZ'
    ;

//Floating Points
FloatingPointNumeral // numerals greater than 1 (according to smtlib format)
    : [2-9] Digit*
    ;

FloatingPointShortVariant //support for the official short variant e.g: (Float128 0)
    : ParOpen ShortFloats '0' ParClose
    ;

NumeralFloatingPoint //standard like (_ FloatingPoint 5 11)
    : ParOpen GRW_Underscore 'FloatingPoint' FloatingPointNumeral FloatingPointNumeral ParClose
    ;

DecimalFloatingPoint //supports formats like: (123.45 or 123e4) TODO: Is the format 123.45 not
// already supported?
    : Decimal + ([eE] [+-]? Digit+)?
    ;

BinaryFloatingPoint // support for formats like: (fp #b0 #b10000 #b1100)
    : ParOpen 'fp' Binary Binary Binary ParClose
    ;

HexadecimalFloatingPoint // support for hexadecimal Floating Points e.g. (#x1.8p+1)
    : '#' 'x' HexDigit+ '.' HexDigit* 'p' [+-]? [0-9]+
    ;

FloatingPointPlusOrMinusInfinity //  Plus and Minus Infinity : e.g. ((_ +oo eb sb) (_
// FloatingPoint eb
// sb))
    : ParOpen ParOpen GRW_Underscore [+-]'oo' FloatingPointNumeral FloatingPointNumeral ParClose
    ParOpen NumeralFloatingPoint ParClose ParClose
    | ParOpen GRW_Underscore [+-]'oo' FloatingPointNumeral FloatingPointNumeral ParClose //short
    // variant e.g. (_ +oo 2 3)
    ;

FloatingPointPlusOrMinusZero // Plus and Minus Zero : ((_ +zero eb sb) (_ FloatingPoint eb sb))
    :ParOpen ParOpen GRW_Underscore [+-]'zero' FloatingPointNumeral FloatingPointNumeral ParClose
     ParOpen GRW_Underscore NumeralFloatingPoint ParClose ParClose
     | ParOpen [+-]'zero' FloatingPointNumeral FloatingPointNumeral ParClose // short variant
     // e.g. (_ +zero 3 )
    ;

NotANumberFloatingPoint // e.g.   ((_ NaN eb sb) (_ FloatingPoint eb sb))
    : ParOpen ParOpen GRW_Underscore 'NaN' FloatingPointNumeral FloatingPointNumeral ParClose
    ParOpen NumeralFloatingPoint ParClose ParClose
    | ParOpen GRW_Underscore 'NaN' FloatingPointNumeral FloatingPointNumeral ParClose
    // e.g. (_ Nan 3 4)
    ;


FloatingPoint //(_ FloatingPoint eb sb)  where eb and sb are numerals greater than 1
     : NumeralFloatingPoint
     | FloatingPointShortVariant
     | DecimalFloatingPoint
     | BinaryFloatingPoint
     | HexadecimalFloatingPoint
     | FloatingPointPlusOrMinusInfinity
     | NotANumberFloatingPoint
     ;


fragment HexDigit
    : '0' .. '9' | 'a' .. 'f' | 'A' .. 'F'
    ;


Colon
    : ':'
    ;

fragment Digit
    : [0-9]
    ;
fragment ShortFloats
    : 'Float16'
    | 'Float32'
    | 'Float64'
    | 'Float128'
    ;

fragment Sym
    : 'a'..'z'
    | 'A' .. 'Z'
    | '+'
    | '='
    | '/'
    | '*'
    | '%'
    | '?'
    | '!'
    | '$'
    | '-'
    | '_'
    | '~'
    | '&'
    | '^'
    | '<'
    | '>'
    | '@'
    | '.'
    ;



fragment BinaryDigit
    : [01]
    ;

fragment PrintableChar
    : '\u0020' .. '\u007E'
    | '\u0080' .. '\uffff'
    | EscapedSpace
    ;

fragment PrintableCharNoDquote
    : '\u0020' .. '\u0021'
    | '\u0023' .. '\u007E'
    | '\u0080' .. '\uffff'
    | EscapedSpace
    ;

fragment PrintableCharNoBackslash
    : '\u0020' .. '\u005B'
    | '\u005D' .. '\u007B'
    | '\u007D' .. '\u007E'
    | '\u0080' .. '\uffff'
    | EscapedSpace
    ;

fragment EscapedSpace
    : '""'
    ;

fragment WhiteSpaceChar
    : '\u0009'
    | '\u000A'
    | '\u000D'
    | '\u0020'
    ;

// Lexer Rules End

// Predefined Keywords



PK_AllStatistics
    : ':all-statistics'
    ;
PK_AssertionStackLevels
    : ':assertion-stack-levels'
    ;
PK_Authors
    : ':authors'
    ;
PK_Category
    : ':category'
    ;
PK_Chainable
    : ':chainable'
    ;
PK_Definition
    : ':definition'
    ;
PK_DiagnosticOutputChannel
    : ':diagnostic-output-channel'
    ;
PK_ErrorBehaviour
    : ':error-behavior'
    ;
PK_Extension
    : ':extensions'
    ;
PK_Funs
    : ':funs'
    ;
PK_FunsDescription
    : ':funs-description'
    ;
PK_GlobalDeclarations
    : ':global-declarations'
    ;
PK_InteractiveMode
    : ':interactive-mode'
    ;
PK_Language
    : ':language'
    ;
PK_LeftAssoc
    : ':left-assoc'
    ;
PK_License
    : ':license'
    ;
PK_Named
    : ':named'
    ;
PK_Name
    : ':name'
    ;
PK_Notes
    : ':notes'
    ;
PK_Pattern
    : ':pattern'
    ;
PK_PrintSuccess
    : ':print-success'
    ;
PK_ProduceAssertions
    : ':produce-assertions'
    ;
PK_ProduceAssignments
    : ':produce-assignments'
    ;
PK_ProduceModels
    : ':produce-models'
    ;
PK_ProduceProofs
    : ':produce-proofs'
    ;
PK_ProduceUnsatAssumptions
    : ':produce-unsat-assumptions'
    ;
PK_ProduceUnsatCores
    : ':produce-unsat-cores'
    ;
PK_RandomSeed
    : ':random-seed'
    ;
PK_ReasonUnknown
    : ':reason-unknown'
    ;
PK_RegularOutputChannel
    : ':regular-output-channel'
    ;
PK_ReproducibleResourceLimit
    : ':reproducible-resource-limit'
    ;
PK_RightAssoc
    : ':right-assoc'
    ;
PK_SmtLibVersion
    : ':smt-lib-version'
    ;
PK_Sorts
    : ':sorts'
    ;
PK_SortsDescription
    : ':sorts-description'
    ;
PK_Source
    : ':source'
    ;
PK_Status
    : ':status'
    ;
PK_Theories
    : ':theories'
    ;
PK_Values
    : ':values'
    ;
PK_Verbosity
    : ':verbosity'
    ;
PK_Version
    : ':version'
    ;

RS_Model //  for model responses
    : 'model'
    ;

UndefinedSymbol:
    Sym (Digit | Sym)*;


// Parser Rules Start

// Starting rule(s)

start
    : logic EOF                                       #start_logic
    | theory_decl EOF                                 #start_theory
    | script EOF                                      #start_script
    | general_response EOF                            #start_gen_resp
    ;

generalReservedWord
    : GRW_Exclamation
    | GRW_Underscore
    | GRW_As
    | GRW_Binary
    | GRW_Decimal
    | GRW_Exists
    | GRW_Hexadecimal
    | GRW_Forall
    | GRW_Let
    | GRW_Match
    | GRW_Numeral
    | GRW_Par
    | GRW_String
    | RS_Model
    ;


simpleSymbol
    : predefSymbol                                          #simp_pre_symb
    | UndefinedSymbol                                       #simp_undef_symb
    ;

quotedSymbol
    : QuotedSymbol
    ;

predefSymbol
    : PS_Not
    | PS_Bool
    | PS_ContinuedExecution
    | PS_Error
    | PS_False
    | PS_ImmediateExit
    | PS_Incomplete
    | PS_Logic
    | PS_Memout
    | PS_Sat
    | PS_Success
    | PS_Theory
    | PS_True
    | PS_Unknown
    | PS_Unsupported
    | PS_Unsat
    ;

predefKeyword
    : PK_AllStatistics
    | PK_AssertionStackLevels
    | PK_Authors
    | PK_Category
    | PK_Chainable
    | PK_Definition
    | PK_DiagnosticOutputChannel
    | PK_ErrorBehaviour
    | PK_Extension
    | PK_Funs
    | PK_FunsDescription
    | PK_GlobalDeclarations
    | PK_InteractiveMode
    | PK_Language
    | PK_LeftAssoc
    | PK_License
    | PK_Named
    | PK_Name
    | PK_Notes
    | PK_Pattern
    | PK_PrintSuccess
    | PK_ProduceAssertions
    | PK_ProduceAssignments
    | PK_ProduceModels
    | PK_ProduceProofs
    | PK_ProduceUnsatAssumptions
    | PK_ProduceUnsatCores
    | PK_RandomSeed
    | PK_ReasonUnknown
    | PK_RegularOutputChannel
    | PK_ReproducibleResourceLimit
    | PK_RightAssoc
    | PK_SmtLibVersion
    | PK_Sorts
    | PK_SortsDescription
    | PK_Source
    | PK_Status
    | PK_Theories
    | PK_Values
    | PK_Verbosity
    | PK_Version
    ;



symbol
    : simpleSymbol                                                  #simpsymb
    | quotedSymbol                                                  #quotsymb
    ;

numeral
    : Numeral
    ;

decimal
    : Decimal
    ;

hexadecimal
    : HexDecimal
    ;

binary
    : Binary
    ;

string
    : String
    ;

floatingpoint
    : FloatingPoint
    ;

keyword
    : predefKeyword                                                   #pre_key
    | Colon simpleSymbol                                              #key_simsymb
    ;

// S-expression

spec_constant
    : numeral                                                         #spec_constant_num
    | decimal                                                         #spec_constant_dec
    | hexadecimal                                                     #spec_constant_hex
    | binary                                                          #spec_constant_bin
    | string                                                          #spec_constant_string
    | floatingpoint                                                   #spec_constant_floating_point
    ;


s_expr
    : spec_constant                                                   #s_expr_spec
    | symbol                                                          #s_expr_symb
    | keyword                                                         #s_expr_key
    | ParOpen s_expr* ParClose                                        #multi_s_expr
    ;

// Identifiers

index
    : numeral                                                         #idx_num
    | symbol                                                          #idx_symb
    ;

identifier
    : symbol                                                          #id_symb
    | ParOpen GRW_Underscore symbol index+ ParClose                   #id_symb_idx
    ;

// Attributes

attribute_value
    : spec_constant                                                   #attr_spec
    | symbol                                                          #attr_symb
    | ParOpen s_expr* ParClose                                        #attr_s_expr
    ;

attribute
    : keyword                                                         #attr_key
    | keyword attribute_value                                         #attr_key_attr
    ;

// Sorts

sort
    : identifier                                                      #sort_id
    | ParOpen identifier sort+ ParClose                               #multisort
    ;


// Terms and Formulas

qual_identifer
    : identifier                                                      #qual_id
    | ParOpen GRW_As identifier sort ParClose                         #qual_id_sort
    ;

var_binding
    : ParOpen symbol term ParClose
    ;

sorted_var
    : ParOpen symbol sort ParClose
    ;

pattern
    : symbol                                                          #pattern_symb
    | ParOpen symbol symbol+ ParClose                                 #pattern_multisymb
    ;

match_case
    : ParOpen pattern term ParClose
    ;

term
    : spec_constant                                                   #term_spec_const
    | qual_identifer                                                  #term_qual_id
    | ParOpen qual_identifer term+ ParClose                           #multiterm
    | ParOpen GRW_Let ParOpen var_binding+ ParClose term ParClose     #term_let
    | ParOpen GRW_Forall ParOpen sorted_var+ ParClose term ParClose   #term_forall
    | ParOpen GRW_Exists ParOpen sorted_var+ ParClose term ParClose   #term_exists
    | ParOpen GRW_Match term ParOpen match_case+ ParClose ParClose    #term_match
    | ParOpen GRW_Exclamation term attribute+ ParClose                #term_exclam
    | ParOpen floating_point_operations                               #term_floating_point
    ;

// Floating Point Operations

fp_abs : 'fp.abs';
fp_neg : 'fp.neg';
fp_add : 'fp.add' ;
fp_sub : 'fp.sub' ;
fp_mul : 'fp.mul' ;
fp_div : 'fp.div' ;
fp_fma : 'fp.fma'; //fused multiplication and addition
fp_sqrt : 'fp.sqrt';
fp_rem: 'fp.rem'; //remainder
fp_roundToIntegral: 'fp.roundToIntegral';
fp_min: 'fp.min';
fp_max: 'fp.max';
fp_leq: 'fp.leq';
fp_lt: 'fp.lt';
fp_geq: 'fp.geq';
fp_gt: 'fp.gt';
fp_eq  : 'fp.eq'  ;
fp_isNormal: 'fp.isNormal';
fp_isSubnormal: 'fp.isSubnormal';
fp_isZero: 'fp.isZero';
fp_isInfinite: 'fp.isInfinite';
fp_isNegative: 'fp.isNegative';
fp_isPositive: 'fp.isPositive';



floating_point_operator_with_1_input // f(x) = x e.g. fp.isNegative(x) = Bool
:fp_abs
|fp_neg
|fp_isNormal
|fp_isSubnormal
|fp_isZero
|fp_isInfinite
|fp_isNegative
|fp_isPositive
;

floating_point_operator_with_2_inputs // f(x,y) = z e.g. fp.add
:fp_rem
|fp_min
|fp_max
|fp_leq
|fp_lt
|fp_geq
|fp_gt
|fp_eq
;

floating_points_with_RM_1_input
:fp_sqrt
|fp_roundToIntegral
;

floating_points_with_RM_2_inputs
:fp_add
|fp_sub
|fp_mul
|fp_div
;

floating_point_funs_with_RM_3_inputs
:fp_fma
;


floating_point_operations //TODO: Check if only Numeral Floating Points are accepted
: ParOpen floating_point_operator_with_1_input FloatingPoint ParClose
| ParOpen floating_point_operator_with_2_inputs FloatingPoint FloatingPoint ParClose
| ParOpen floating_points_with_RM_1_input RoundingModes FloatingPoint ParClose
| ParOpen floating_points_with_RM_2_inputs RoundingModes FloatingPoint FloatingPoint ParClose
| ParOpen floating_point_funs_with_RM_3_inputs RoundingModes FloatingPoint FloatingPoint
FloatingPoint ParClose
|floating_point_conversions
;


//Floating Point Conversions (to_fp functions)

floating_point_conversions
: from_fp_operations
| to_fp_operations
;

to_fp_input
: ParOpen GRW_Underscore 'to_fp' FloatingPointNumeral FloatingPointNumeral ParClose
;

to_fp_operations //REMEMBER THAT ALL CONVERSIONS ARE UNSPECIFIED FOR NAN AND INFINITY VALUES
: ParOpen to_fp_input Binary ParClose
|ParOpen to_fp_input RoundingModes NumeralFloatingPoint ParClose
|ParOpen to_fp_input RoundingModes Real ParClose
|ParOpen to_fp_input RoundingModes Binary ParClose //if the bitvec should be interpreted as 2^n
|//unsigned integers don't exist in Java so we don't allow them
;

from_fp_operations
:ParOpen ParOpen GRW_Underscore 'fp.to_sbv' FloatingPointNumeral ParClose RoundingModes NumeralFloatingPoint
;

// Theory Declarations

sort_symbol_decl
    : ParOpen identifier numeral attribute* ParClose;

meta_spec_constant
    : GRW_Numeral
    | GRW_Decimal
    | GRW_String
    ;

fun_symbol_decl
    : ParOpen spec_constant sort attribute* ParClose                      #fun_symb_spec
    | ParOpen meta_spec_constant sort attribute* ParClose                 #fun_symb_meta
    | ParOpen identifier sort+ attribute* ParClose                        #fun_symb_id
    ;

par_fun_symbol_decl
    : fun_symbol_decl                                                     #par_fun_symb
    | ParOpen GRW_Par ParOpen symbol+ ParClose ParOpen identifier sort+
    attribute* ParClose ParClose                                          #par_fun_multi_symb
    ;

theory_attribute
    : PK_Sorts ParOpen sort_symbol_decl+ ParClose                         #theory_sort
    | PK_Funs ParOpen par_fun_symbol_decl+ ParClose                       #theory_fun
    | PK_SortsDescription string                                          #theory_sort_descr
    | PK_FunsDescription string                                           #theory_fun_descr
    | PK_Definition string                                                #theory_def
    | PK_Values string                                                    #theory_val
    | PK_Notes string                                                     #theory_notes
    | attribute                                                           #theory_attr
    ;

theory_decl
    : ParOpen PS_Theory symbol theory_attribute+ ParClose
    ;


// Logic Declarations

logic_attribue
    : PK_Theories ParOpen symbol+ ParClose                                #logic_theory
    | PK_Language string                                                  #logic_language
    | PK_Extension string                                                 #logic_ext
    | PK_Values string                                                    #logic_val
    | PK_Notes string                                                     #logic_notes
    | attribute                                                           #logic_attr
    ;

logic
    : ParOpen PS_Logic symbol logic_attribue+ ParClose
    ;


// Scripts

sort_dec
    : ParOpen symbol numeral ParClose
    ;

selector_dec
    : ParOpen symbol sort ParClose
    ;

constructor_dec
    : ParOpen symbol selector_dec* ParClose
    ;

datatype_dec
    : ParOpen constructor_dec+ ParClose                                         #data_constr
    | ParOpen GRW_Par ParOpen symbol+ ParClose ParOpen constructor_dec+
    ParClose ParClose                                                           #data_multisymb
    ;

function_dec
    : ParOpen symbol ParOpen sorted_var* ParClose sort ParClose
    ;

function_def
    : symbol ParOpen sorted_var* ParClose sort term
    ;

prop_literal
    : symbol                                                                    #prop_symb
    | ParOpen PS_Not symbol ParClose                                            #prop_not
    ;


script
    : command*
    ;

cmd_assert
    : CMD_Assert term
    ;

cmd_checkSat
    : CMD_CheckSat
    ;

cmd_checkSatAssuming
    : CMD_CheckSatAssuming ParOpen prop_literal* ParClose
    ;

cmd_declareConst
    : CMD_DeclareConst symbol sort
    ;

cmd_declareDatatype
    : CMD_DeclareDatatype symbol datatype_dec
    ;

cmd_declareDatatypes
    // cardinalitiees for sort_dec and datatype_dec have to be n+1
    : CMD_DeclareDatatypes ParOpen sort_dec+ ParClose ParOpen datatype_dec+ ParClose
    ;

cmd_declareFun
    : CMD_DeclareFun symbol ParOpen sort* ParClose sort
    ;

cmd_declareSort
    : CMD_DeclareSort symbol numeral
    ;

cmd_defineFun
    : CMD_DefineFun function_def
    ;

cmd_defineFunRec
    : CMD_DefineFunRec function_def
    ;

cmd_defineFunsRec
    // cardinalitiees for function_dec and term have to be n+1
    : CMD_DefineFunsRec ParOpen function_dec+ ParClose ParOpen term+ ParClose
    ;

cmd_defineSort
    : CMD_DefineSort symbol ParOpen symbol* ParClose sort
    ;

cmd_echo
    : CMD_Echo string
    ;

cmd_exit
    : CMD_Exit
    ;

cmd_getAssertions
    : CMD_GetAssertions
    ;

cmd_getAssignment
    : CMD_GetAssignment
    ;

cmd_getInfo
    : CMD_GetInfo info_flag
    ;

cmd_getModel
    : CMD_GetModel
    ;

cmd_getOption
    : CMD_GetOption keyword
    ;

cmd_getProof
    : CMD_GetProof
    ;

cmd_getUnsatAssumptions
    : CMD_GetUnsatAssumptions
    ;

cmd_getUnsatCore
    : CMD_GetUnsatCore
    ;

cmd_getValue
    : CMD_GetValue ParOpen term+ ParClose
    ;

cmd_pop
    : CMD_Pop numeral
    ;

cmd_push
    : CMD_Push numeral
    ;

cmd_reset
    : CMD_Reset
    ;

cmd_resetAssertions
    : CMD_ResetAssertions
    ;

cmd_setInfo
    : CMD_SetInfo attribute
    ;

cmd_setLogic
    : CMD_SetLogic symbol
    ;

cmd_setOption
    : CMD_SetOption option
    ;

command
    : ParOpen cmd_assert ParClose                           #assert
    | ParOpen cmd_checkSat ParClose                         #check
    | ParOpen cmd_checkSatAssuming ParClose                 #check_assume
    | ParOpen cmd_declareConst ParClose                     #decl_const
    | ParOpen cmd_declareDatatype ParClose                  #decl_data
    | ParOpen cmd_declareDatatypes ParClose                 #decl_datas
    | ParOpen cmd_declareFun ParClose                       #decl_fun
    | ParOpen cmd_declareSort ParClose                      #decl_sort
    | ParOpen cmd_defineFun ParClose                        #def_fun
    | ParOpen cmd_defineFunRec ParClose                     #def_fun_rec
    | ParOpen cmd_defineFunsRec ParClose                    #def_funs_rec
    | ParOpen cmd_defineSort ParClose                       #def_sort
    | ParOpen cmd_echo ParClose                             #echo
    | ParOpen cmd_exit ParClose                             #exit
    | ParOpen cmd_getAssertions ParClose                    #get_assert
    | ParOpen cmd_getAssignment ParClose                    #get_assign
    | ParOpen cmd_getInfo ParClose                          #get_info
    | ParOpen cmd_getModel ParClose                         #get_model
    | ParOpen cmd_getOption ParClose                        #get_option
    | ParOpen cmd_getProof ParClose                         #get_proof
    | ParOpen cmd_getUnsatAssumptions ParClose              #get_unsat_assume
    | ParOpen cmd_getUnsatCore ParClose                     #get_unsat_core
    | ParOpen cmd_getValue ParClose                         #get_val
    | ParOpen cmd_pop ParClose                              #pop
    | ParOpen cmd_push ParClose                             #push
    | ParOpen cmd_reset ParClose                            #reset
    | ParOpen cmd_resetAssertions ParClose                  #reset_assert
    | ParOpen cmd_setInfo ParClose                          #setInfo
    | ParOpen cmd_setLogic ParClose                         #set_logic
    | ParOpen cmd_setOption ParClose                        #set_option
    ;


b_value
    : PS_True
    | PS_False
    ;

option
    : PK_DiagnosticOutputChannel string             #diagnose
    | PK_GlobalDeclarations b_value                 #global
    | PK_InteractiveMode b_value                    #interactive
    | PK_PrintSuccess b_value                       #print_succ
    | PK_ProduceAssertions b_value                  #prod_assert
    | PK_ProduceAssignments b_value                 #prod_assign
    | PK_ProduceModels b_value                      #prod_mod
    | PK_ProduceProofs b_value                      #prod_proofs
    | PK_ProduceUnsatAssumptions b_value            #prod_unsat_assume
    | PK_ProduceUnsatCores b_value                  #prod_unsat_core
    | PK_RandomSeed numeral                         #rand_seed
    | PK_RegularOutputChannel string                #reg_out
    | PK_ReproducibleResourceLimit numeral          #repro
    | PK_Verbosity numeral                          #verbose
    | attribute                                     #opt_attr
    ;

info_flag
    : PK_AllStatistics                              #all_stat
    | PK_AssertionStackLevels                       #assert_stack
    | PK_Authors                                    #authors
    | PK_ErrorBehaviour                             #error
    | PK_Name                                       #name
    | PK_ReasonUnknown                              #r_unknown
    | PK_Version                                    #version
    | keyword                                       #info_key
    ;

// responses

error_behaviour
    : PS_ImmediateExit
    | PS_ContinuedExecution
    ;

reason_unknown
    : PS_Memout                                   #memout
    | PS_Incomplete                               #incomp
    | s_expr                                      #r_unnown_s_expr
    ;

model_response
    : ParOpen cmd_defineFun ParClose              #resp_def_fun
    | ParOpen cmd_defineFunRec ParClose           #resp_def_fun_rec
    | ParOpen cmd_defineFunsRec ParClose          #resp_def_funs_rec
    ;

info_response
    : PK_AssertionStackLevels numeral             #info_assert_stack
    | PK_Authors string                           #info_authors
    | PK_ErrorBehaviour error_behaviour           #info_error
    | PK_Name string                              #info_name
    | PK_ReasonUnknown reason_unknown             #info_r_unknown
    | PK_Version string                           #info_version
    | attribute                                   #info_attr
    ;

valuation_pair
    : ParOpen term term ParClose
    ;

t_valuation_pair
    : ParOpen symbol b_value ParClose
    ;

check_sat_response
    : PS_Sat
    | PS_Unsat
    | PS_Unknown
    ;

echo_response
    : string
    ;

get_assertions_response
    : ParOpen term* ParClose
    ;

get_assignment_response
    : ParOpen t_valuation_pair* ParClose
    ;

get_info_response
    : ParOpen info_response+ ParClose
    ;

get_model_response
    : ParOpen RS_Model model_response* ParClose       #rs_model
    | ParOpen model_response* ParClose                #model_resp
    ;

get_option_response
    : attribute_value
    ;

get_proof_response
    : s_expr
    ;

get_unsat_assump_response
    : ParOpen symbol* ParClose
    ;

get_unsat_core_response
    : ParOpen symbol* ParClose
    ;

get_value_response
    : ParOpen valuation_pair+ ParClose
    ;

specific_success_response
    : check_sat_response                      #resp_check_sat
    | echo_response                           #resp_echo
    | get_assertions_response                 #resp_get_assert
    | get_assignment_response                 #resp_gett_assign
    | get_info_response                       #resp_get_info
    | get_model_response                      #resp_get_model
    | get_option_response                     #resp_option
    | get_proof_response                      #resp_proof
    | get_unsat_assump_response               #resp_unsat_assume
    | get_unsat_core_response                 #resp_unsat_core
    | get_value_response                      #resp_value
    ;

general_response
    : PS_Success                              #resp_success
    | specific_success_response               #resp_spec_successs
    | PS_Unsupported                          #resp_unsupported
    | ParOpen PS_Error string ParClose        #resp_error
    ;


// Parser Rules End

WS  :  [ \t\r\n]+ -> skip
    ;