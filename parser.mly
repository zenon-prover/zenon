/*  Copyright 2004 INRIA  */

%{
Version.add "$Id: parser.mly,v 1.5 2004-05-26 16:22:36 doligez Exp $";;

open Expr;;
open Phrase;;

let rec mk_quant q vs body =
  match vs with
  | [] -> body
  | h::t -> q (h, "", mk_quant q t body)
;;

let rec myfold f e el =
  match el with
  | [] -> e
  | h::t -> f (e, myfold f h t)
;;

let mkand e el = myfold eand e el;;
let mkor e el = myfold eor e el;;
let mkimply e el = myfold eimply e el;;
let mkequiv e el = myfold eequiv e el;;

%}

%token OPEN
%token CLOSE
%token <string> IDENT
%token <string> STRING
%token <int> INT
%token DEF
%token GOAL
%token NOT
%token AND
%token OR
%token IMPLY
%token EQUIV
%token TRUE
%token FALSE
%token ALL
%token EX
%token TAU
%token EQUAL
%token EOF

%token INCLUDE
%token DOT
%token INPUT_CLAUSE
%token INPUT_FORMULA
%token LBRACKET
%token RBRACKET
%token <string> LIDENT
%token <string> UIDENT
%token POSITIVE
%token NEGATIVE
%token COMMA
%token COLON
%token RIMPLY
%token XOR
%token NOR
%token NAND

%token TOBE
%token QED
%token BY
%token BYDEF
%token COLONEQUAL
%token ARROW
%token DOUBLEARROW
%token FORALL
%token LET
%token IN
%token TILDE

%nonassoc forall
%nonassoc AND
%right ARROW DOUBLEARROW
%nonassoc TILDE

%start theory
%type <Phrase.phrase list> theory

%start phrase
%type <Phrase.phrase> phrase

%start tpfile
%type <Phrase.tpphrase list> tpfile

%start coqfile
%type <Phrase.phrase list> coqfile

%%

/* Native LISP-like syntax */

theory:
  | EOF               { [] }
  | phrase theory     { $1 :: $2 }
;

phrase:
  | DEF IDENT OPEN ident_list CLOSE expr { Def (DefReal ($2, $4, $6)) }
  | INT expr                             { Hyp ($2, $1) }
  | GOAL expr                            { Globals.goal_found := true;
                                           Hyp (enot $2, 0) }
  | expr                                 { Hyp ($1, 1) }
;

expr:
  | IDENT                                { evar $1 }
  | OPEN IDENT expr_list CLOSE           { eapp ($2, $3) }
  | OPEN NOT expr CLOSE                  { enot ($3) }
  | OPEN AND expr expr_list CLOSE        { mkand $3 $4 }
  | OPEN OR expr expr_list CLOSE         { mkor $3 $4 }
  | OPEN IMPLY expr expr_list CLOSE      { mkimply $3 $4 }
  | OPEN EQUIV expr expr_list CLOSE      { mkequiv $3 $4 }
  | OPEN TRUE CLOSE                      { etrue }
  | TRUE                                 { etrue }
  | OPEN FALSE CLOSE                     { efalse }
  | FALSE                                { efalse }
  | OPEN ALL lambda CLOSE                { eall $3 }
  | OPEN EX lambda CLOSE                 { eex $3 }
  | OPEN TAU lambda CLOSE                { etau $3 }
  | OPEN EQUAL expr expr CLOSE           { eapp ("=", [$3; $4]) }
;

expr_list:
  | expr expr_list     { $1 :: $2 }
  | /* empty */        { [] }
;

lambda:
  | OPEN OPEN IDENT STRING CLOSE expr CLOSE      { ($3, $4, $6) }
  | OPEN OPEN IDENT CLOSE expr CLOSE             { ($3, "", $5) }
;

ident_list:
  | /* empty */       { [] }
  | IDENT ident_list  { $1 :: $2 }
;


/* TPTP syntax */

tpfile:
  | EOF               { [] }
  | tpphrase tpfile   { $1 :: $2 }
;
tpphrase:
  | INCLUDE OPEN STRING CLOSE DOT  { Phrase.Include $3 }
  | INPUT_CLAUSE OPEN LIDENT COMMA LIDENT COMMA LBRACKET tpliterals RBRACKET
    CLOSE DOT                      { Phrase.Clause ($3, $5, $8) }
  | INPUT_FORMULA OPEN LIDENT COMMA LIDENT COMMA tpformula CLOSE DOT
                                   { Phrase.Formula ($3, $5, $7) }
;
tpliterals:
  | tpliteral COMMA tpliterals  { $1 :: $3 }
  | tpliteral                   { [$1] }
;
tpliteral:
  | POSITIVE tpexpr   { $2 }
  | NEGATIVE tpexpr   { enot ($2) }
;
tpexpr:
  | UIDENT                                 { evar ($1) }
  | LIDENT tparguments                     { eapp ($1, $2) }
  | EQUAL OPEN tpexpr COMMA tpexpr CLOSE   { eapp ("=", [$3; $5]) }
;
tparguments:
  | OPEN tpexpr_list CLOSE         { $2 }
  | /* empty */                    { [] }
;
tpexpr_list:
  | tpexpr COMMA tpexpr_list       { $1 :: $3 }
  | tpexpr                         { [$1] }
;
tpformula:
  | tpatom                         { $1 }
  | tpatom AND tpformula           { eand ($1, $3) }
  | tpatom OR tpformula            { eor ($1, $3) }
  | tpatom IMPLY tpformula         { eimply ($1, $3) }
  | tpatom EQUIV tpformula         { eequiv ($1, $3) }
  | tpatom RIMPLY tpformula        { eimply ($3, $1) }
  | tpatom XOR tpformula           { enot (eequiv ($1, $3)) }
  | tpatom NOR tpformula           { enot (eor ($1, $3)) }
  | tpatom NAND tpformula          { enot (eand ($1, $3)) }
;
tpatom:
  | ALL LBRACKET tpvar_list RBRACKET COLON tpatom
                                   { mk_quant eall $3 $6 }
  | EX LBRACKET tpvar_list RBRACKET COLON tpatom
                                   { mk_quant eex $3 $6 }
  | NOT tpatom                     { enot ($2) }
  | OPEN tpformula CLOSE           { $2 }
  | tpexpr                         { $1 }
;
tpvar_list:
  | UIDENT COMMA tpvar_list        { $1 :: $3 }
  | UIDENT                         { [$1] }
;


/* Coq Syntax */

coqfile:
  | TOBE coqexpr BY coqhyp_list BYDEF coqdef_list QED opt_dot EOF
      { Hyp (enot $2, 0) :: $4 @ $6 }
;
coqexpr:
  | OPEN coqexpr CLOSE
      { $2 }
  | OPEN IDENT COLON IDENT CLOSE coqexpr %prec forall
      { eall ($2, $4, $6) }
  | coqapplication
      { eapp $1 }
  | TILDE coqexpr
      { enot ($2) }
  | OPEN AND coqexpr coqexpr CLOSE
      { eand ($3, $4) }
  | OPEN OR coqexpr coqexpr CLOSE
      { eor ($3, $4) }
  | OPEN EQUAL coqexpr coqexpr CLOSE
      { eapp ("=", [$3; $4]) }
  | IDENT
      { evar ($1) }
  | coqexpr ARROW coqexpr
      { eimply ($1, $3) }
  | coqexpr DOUBLEARROW coqexpr
      { eequiv ($1, $3) }
  /* FIXME TODO voir comment coder les let-in */
  | LET IDENT COLONEQUAL coqexpr IN coqexpr %prec forall
      { Expr.substitute [($2, $4)] $6 }
;
coqapplication:
  | OPEN IDENT coqexpr_list1 CLOSE
      { ($2, $3) }
  | OPEN coqapplication coqexpr_list1 CLOSE
      { let (sym, args1) = $2 in (sym, args1 @ $3) }
;
coqexpr_list1:
  | coqexpr              { [$1] }
  | coqexpr coqexpr_list1 { $1 :: $2 }
;
coqhyp:
  | IDENT COLON coqexpr  { Hyp ($3, 1) }
;
coqhyp_list:
  | /* empty */          { [] }
  | coqhyp coqhyp_list   { $1 :: $2 }
;
coqdef:
  | IDENT COLONEQUAL coqparam_expr
      { let (params, expr) = $3 in Def (DefReal ($1, params, expr)) }
;
coqparam_expr:
  | coqexpr
      { ([], $1) }
  | LBRACKET IDENT COLON IDENT RBRACKET coqparam_expr
      { let (params, expr) = $6 in ($2 :: params, expr) }
;
coqdef_list:
  | /* empty */           { [] }
  | coqdef coqdef_list    { $1 :: $2 }
;
opt_dot:
  | DOT                   { () }
  | /* empty */           { () }
;
%%
