/*  Copyright 2005 INRIA  */

%{
Version.add "$Id: parsezen.mly,v 1.3 2006-02-02 22:13:54 doligez Exp $";;

open Printf;;

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
let mkrimply e el = myfold (fun (a, b) -> eimply (b, a)) e el;;

let mk_ealln (vars, typ, body) =
  let f v b = ealln (v, typ, b) in
  List.fold_right f vars body
;;

let mk_eexn (vars, typ, body) =
  let f v b = eexn (v, typ, b) in
  List.fold_right f vars body
;;

let hyp_counter = ref 0;;
let gen_hyp_name () =
  incr hyp_counter;
  sprintf "A'%d" !hyp_counter
;;

%}

%token OPEN
%token CLOSE
%token <string> IDENT
%token <string> STRING
%token <int> INT
%token DEF
%token GOAL
%token SIG
%token NOT
%token AND
%token OR
%token IMPLY
%token RIMPLY
%token EQUIV
%token TRUE
%token FALSE
%token ALL
%token EX
%token TAU
%token EQUAL
%token EOF

%start file
%type <Phrase.phrase list> file

%%

file:
  | EOF               { [] }
  | phrase file       { $1 :: $2 }
;

phrase:
  | DEF OPEN IDENT ident_list CLOSE expr { Def (DefReal ($3, $4, $6)) }
  | int_opt hyp_name expr                { Hyp ($2, $3, $1) }
  | GOAL expr                            { Hyp ("z'g", enot $2, 0) }
  | SIG IDENT OPEN string_list CLOSE STRING { Sig ($2, $4, $6) }
;

expr:
  | IDENT                                { evar $1 }
  | OPEN IDENT expr_list CLOSE           { eapp ($2, $3) }
  | OPEN NOT expr CLOSE                  { enot ($3) }
  | OPEN AND expr expr_list CLOSE        { mkand $3 $4 }
  | OPEN OR expr expr_list CLOSE         { mkor $3 $4 }
  | OPEN IMPLY expr expr_list CLOSE      { mkimply $3 $4 }
  | OPEN RIMPLY expr expr_list CLOSE     { mkrimply $3 $4 }
  | OPEN EQUIV expr expr_list CLOSE      { mkequiv $3 $4 }
  | OPEN TRUE CLOSE                      { etrue }
  | TRUE                                 { etrue }
  | OPEN FALSE CLOSE                     { efalse }
  | FALSE                                { efalse }
  | OPEN ALL mlambda CLOSE               { mk_ealln $3 }
  | OPEN EX mlambda CLOSE                { mk_eexn $3 }
  | OPEN TAU lambda CLOSE                { etau $3 }
  | OPEN EQUAL expr expr CLOSE           { eapp ("=", [$3; $4]) }
;

expr_list:
  | expr expr_list     { $1 :: $2 }
  | /* empty */        { [] }
;

lambda:
  | OPEN OPEN IDENT STRING CLOSE expr CLOSE      { (evar $3, $4, $6) }
  | OPEN OPEN IDENT CLOSE expr CLOSE             { (evar $3, "", $5) }
;

mlambda:
  | OPEN OPEN ident_list STRING CLOSE expr CLOSE { ($3, $4, $6) }
  | OPEN OPEN ident_list CLOSE expr CLOSE        { ($3, "", $5) }
;

ident_list:
  | /* empty */       { [] }
  | IDENT ident_list  { evar $1 :: $2 }
;

int_opt:
  | /* empty */       { 1 }
  | INT               { $1 }
;

hyp_name:
  | /* empty */       { gen_hyp_name () }
  | STRING            { $1 }
;

string_list:
  | /* empty */         { [] }
  | STRING string_list  { $1 :: $2 }
;
%%
