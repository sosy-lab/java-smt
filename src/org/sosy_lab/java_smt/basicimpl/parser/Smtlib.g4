/*
 * This file is part of JavaSMT,
 * an API wrapper for a collection of SMT solvers:
 * https://github.com/sosy-lab/java-smt
 *
 * SPDX-FileCopyrightText: 2025 Dirk Beyer <https://www.sosy-lab.org>
 *
 * SPDX-License-Identifier: Apache-2.0
 */

grammar Smtlib;

Comment
    : ';' ~[\n\r]* -> skip
    ;

White
    : [ \t\r\n]+ -> skip
    ;

boolean
    : 'true'
    | 'false'
    ;

fragment BinaryDigit
    : [01]
    ;

Binary
    : '#b' BinaryDigit+
    ;

fragment HexDigit
    : '0'..'9'
    | 'a'..'f'
    | 'A'..'F'
    ;

HexaDecimal
    : '#x' HexDigit+
    ;

bitvec
    : Binary
    | HexaDecimal
    ;

float
    : '(' 'fp' bitvec bitvec bitvec ')'
    ;

fragment Digit
    : [0-9]
    ;

Numeral
    : '0'
    | [1-9] Digit*
    ;

integer
    : Numeral
    ;

Decimal
    : Numeral '.' '0'* Numeral
    ;

real
    : Decimal
    ;

literal
    : boolean
    | integer
    | real
    | bitvec
    | float
    ;

fragment Sym
    : 'a'..'z'
    | 'A'..'Z'
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

Simple
    : Sym (Sym | Digit)*
    ;

fragment QuotedChar
    : '\u0009'             // \t
    | '\u000A'             // \n
    | '\u000D'             // \r
    | '\u0020' .. '\u005B' // Skip '\'
    | '\u005D' .. '\u007B' // Skip '|'
    | '\u007D' .. '\u007E' // Skip <Delete>
    | '\u0080' .. '\uffff'
    ;

Quoted
    : '|' QuotedChar* '|'
    ;

symbol
    : Simple
    | Quoted
    ;

Keyword
    : ':' Simple
    ;

keyword
    : Keyword
    ;

sort
    : 'Bool'                                       # SortBool
    | 'Int'                                        # SortInt
    | 'Real'                                       # SortReal
    | '(' '_' 'BitVec' integer ')'                 # SortBitvec
    | ('Float16'
      |'Float32'
      |'Float64'
      |'Float128'
      |'(' '_' 'FloatingPoint' integer integer ')'
      )                                            # SortFloat
    | '(' 'Array' sort sort ')'                    # SortArray
    ;

quantifier
    : 'forall'
    | 'exists'
    ;

sortedVar
    : '(' symbol sort ')'
    ;

binding
    : '(' symbol expr ')'
    ;

attribute
    : keyword expr?
    ;

expr
    : literal                                    # Const
    | symbol                                     # Var
    | '(' '_' symbol integer+ ')'                # Indexed
    | '(' 'as' symbol sort ')'                   # As
    | '(' '!' expr attribute+ ')'                # Annotated
    | '(' 'let' '(' binding+ ')' expr ')'        # Let
    | '(' quantifier '(' sortedVar+ ')' expr ')' # Quantified
    | '(' expr expr+ ')'                         # App
    ;

setInfo
    : '(' 'set-info' attribute ')'
    ;

setOption
    : '(' 'set-option' attribute ')'
    ;

setLogic
    : '(' 'set-logic' symbol ')'
    ;

declare
    : '(' 'declare-const' symbol sort ')'
    | '(' 'declare-fun' symbol '(' sort* ')' sort ')'
    ;

define
    : '(' 'define-const' symbol sort expr ')'
    | '(' 'define-fun' symbol '(' sortedVar* ')' sort expr ')'
    ;

assert
    : '(' 'assert' expr ')'
    ;

command
    : setInfo
    | setOption
    | setLogic
    | declare
    | define
    | assert
    ;

smtlib
    : command* EOF
    ;
