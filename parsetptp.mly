/*  Copyright 2005 INRIA  */

%{
Version.add "$Id: parsetptp.mly,v 1.2 2005-11-05 11:13:17 doligez Exp $";;

open Printf;;

open Expr;;
open Phrase;;

let rec mk_quant q vs body =
  match vs with
  | [] -> body
  | h::t -> q (h, "", mk_quant q t body)
;;

%}

%token EQUIV
%token IMPLY
%token RIMPLY
%token AND
%token OR
%token NOT
%token ALL
%token EX
%token EQUAL
%token OPEN
%token CLOSE
%token <string> STRING
%token EOF
%token INCLUDE
%token DOT
%token INPUT_CLAUSE
%token INPUT_FORMULA
%token FOF
%token AXIOM
%token HYPOTHESIS
%token CONJECTURE
%token LBRACKET
%token RBRACKET
%token <string> LIDENT
%token <string> UIDENT
%token POSITIVE
%token NEGATIVE
%token COMMA
%token EQSYM
%token NEQSYM
%token COLON
%token XOR
%token NOR
%token NAND
%token NEQUAL
%token <string> TPANNOT

%nonassoc OPEN
%nonassoc ALL EXISTS
%nonassoc EQSYM NEQSYM
%left XOR NOR NAND AND OR
%right IMPLY
%left RIMPLY
%nonassoc EQUIV
%nonassoc lowest

%start file
%type <Phrase.tpphrase list> file

%%

/* TPTP (v3.x) syntax */

file:
  | EOF             { [] }
  | phrase file     { $1 :: $2 }
;
phrase:
  | INCLUDE OPEN STRING CLOSE DOT  { Phrase.Include $3 }
  | INPUT_FORMULA OPEN LIDENT COMMA LIDENT COMMA formula CLOSE DOT
                                   { Phrase.Formula ($3, $5, $7) }
  | TPANNOT                        { Phrase.Annotation $1 }
;
expr:
  | UIDENT                             { evar ($1) }
  | LIDENT arguments                   { eapp ($1, $2) }
  | EQUAL OPEN expr COMMA expr CLOSE   { eapp ("=", [$3; $5]) }
  | expr EQSYM expr                    { eapp ("=", [$1; $3]) }
  | expr NEQSYM expr                   { enot (eapp ("=", [$1; $3])) }
;
arguments:
  | OPEN expr_list CLOSE         { $2 }
  | /* empty */                  { [] }
;
expr_list:
  | expr COMMA expr_list         { $1 :: $3 }
  | expr                         { [$1] }
;
formula:
  | atom %prec lowest          { $1 }
  | atom AND formula           { eand ($1, $3) }
  | atom OR formula            { eor ($1, $3) }
  | atom IMPLY formula         { eimply ($1, $3) }
  | atom EQUIV formula         { eequiv ($1, $3) }
  | atom RIMPLY formula        { eimply ($3, $1) }
  | atom XOR formula           { enot (eequiv ($1, $3)) }
  | atom NOR formula           { enot (eor ($1, $3)) }
  | atom NAND formula          { enot (eand ($1, $3)) }
;
atom:
  | ALL LBRACKET var_list RBRACKET COLON atom
                                   { mk_quant ealln $3 $6 }
  | EX LBRACKET var_list RBRACKET COLON atom
                                   { mk_quant eexn $3 $6 }
  | NOT atom                       { enot ($2) }
  | OPEN formula CLOSE             { $2 }
  | expr                           { $1 }
;
var_list:
  | UIDENT COMMA var_list          { evar $1 :: $3 }
  | UIDENT                         { [evar $1] }
;

%%
