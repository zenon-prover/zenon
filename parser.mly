/*  Copyright 2004 INRIA  */

%{
Version.add "$Id: parser.mly,v 1.21 2005-07-21 15:28:59 prevosto Exp $";;

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

let hyp_counter = ref 0;;

let rec mk_type_string e =
  match e with
  | Evar (s, _) -> s
  | Emeta _ -> assert false
  | Eapp (s, args, _) ->
      List.fold_left (fun s a -> sprintf "%s %s" s (mk_type_string a)) s args
  | _ -> assert false (* FIXME TODO *)
;;

let coq_eapp (s, args) =
  match (s, args) with
  | "and", [e1; e2] -> eand (e1, e2)
  | "or", [e1; e2] -> eor (e1, e2)
  | "not", [e1] -> enot (e1)
  | _ -> eapp (s, args)
;;

let mk_coq_apply (e, l) =
  match e with
  | Eapp (s, args, _) -> coq_eapp (s, args @ l)
  | Evar (s, _) -> coq_eapp (s, l)
  | _ -> raise Parse_error
;;

let mk_coq_all bindings body =
  let f (var, ty) e = eall (evar var, ty, e) in
  List.fold_right f bindings body
;;

let mk_coq_ex bindings body =
  let f (var, ty) e = eex (evar var, ty, e) in
  List.fold_right f bindings body
;;

let mk_coq_let id expr body =
  substitute [(evar id, expr)] body
;;

%}

/* tokens for parsing coq syntax */

%token BANG_
%token PERCENT_
%token AMPER_
%token AMPER_AMPER_
%token LPAREN_
%token LPAREN_RPAREN_
%token RPAREN_
%token STAR_
%token PLUS_
%token PLUS_PLUS_
%token COMMA_
%token DASH_
%token DASH_GT_
%token PERIOD_
%token PERIOD_LPAREN_
%token PERIOD_PERIOD_
%token SLASH_
%token SLASH_BACKSL_
%token COLON_
%token COLON_COLON_
%token COLON_LT_
%token COLON_EQ_
%token COLON_GT_
%token SEMI_
%token LT_
%token LT_DASH_
%token LT_DASH_GT_
%token LT_COLON_
%token LT_EQ_
%token LT_GT_
%token EQ_
%token EQ_GT_
%token EQ_UNDER_D_
%token GT_
%token GT_DASH_GT_
%token GT_EQ_
%token QUEST_
%token QUEST_EQ_
%token AROBAS_
%token LBRACK_
%token BACKSL_SLASH_
%token RBRACK_
%token HAT_
%token LBRACE_
%token BAR_
%token BAR_DASH_
%token BAR_BAR_
%token RBRACE_
%token TILDE_

%token AS
%token AT
%token COFIX
%token DEFINITION
%token DEPENDS
%token ELSE
%token END
%token EXISTS
%token EXISTS2
%token FIX
%token FOR
%token FORALL
%token FUN
%token IF
%token UC_IF
%token IN
%token LET
%token MATCH
%token MOD
%token ON
%token PARAMETER
%token PROP
%token RETURN
%token SET
%token THEN
%token TYPE
%token USING
%token WHERE
%token WITH

%token <string> BEGINPROOF
%token ENDPROOF

/* tokens for zenon syntax */

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
%token RIMPLY
%token EQUIV
%token TRUE
%token FALSE
%token ALL
%token EX
%token TAU
%token EQUAL
%token EOF

/* tokens for TPTP syntax */

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
%token EQSYM
%token NEQSYM
%token COLON
%token XOR
%token NOR
%token NAND
%token <string> TPANNOT

/* precedences for TPTP */
%nonassoc OPEN
%nonassoc ALL EXISTS
%nonassoc EQSYM NEQSYM
%left XOR NOR NAND AND OR
%right IMPLY
%left RIMPLY
%nonassoc EQUIV
%nonassoc lowest

/* precedences for coq syntax */

%nonassoc LPAREN_ IDENT
%nonassoc FORALL EXISTS COMMA_ IF THEN ELSE
%right DASH_GT_ LT_DASH_GT_
%right BACKSL_SLASH_
%right SLASH_BACKSL_
%nonassoc EQ_ LT_GT_
%nonassoc TILDE_
%left apply

%start theory
%type <Phrase.phrase list> theory

%start phrase
%type <Phrase.phrase> phrase

%start tpfile
%type <Phrase.tpphrase list> tpfile

%start coqfile
%type <string * Phrase.phrase list> coqfile

%%

/* Native LISP-like syntax */

theory:
  | EOF               { [] }
  | phrase theory     { $1 :: $2 }
;

phrase:
  | DEF IDENT OPEN ident_list CLOSE expr { Def (DefReal ($2, $4, $6)) }
  | int_opt hyp_name expr                { Hyp ($2, $3, $1) }
  | GOAL expr                            { Globals.goal_found := true;
                                           Hyp ("_Zgoal", enot $2, 0) }
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
  | OPEN OPEN IDENT STRING CLOSE expr CLOSE      { (evar $3, $4, $6) }
  | OPEN OPEN IDENT CLOSE expr CLOSE             { (evar $3, "", $5) }
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
  | /* empty */       { incr hyp_counter; Printf.sprintf "_hyp%d" !hyp_counter }
  | STRING            { incr hyp_counter; $1 }

/* TPTP syntax */

tpfile:
  | EOF               { [] }
  | tpphrase tpfile   { $1 :: $2 }
;
tpphrase:
  | INCLUDE OPEN STRING CLOSE DOT  { Phrase.Include $3 }
  | INPUT_FORMULA OPEN LIDENT COMMA LIDENT COMMA tpformula CLOSE DOT
                                   { Phrase.Formula ($3, $5, $7) }
  | TPANNOT                        { Phrase.Annotation $1 }
;
tpexpr:
  | UIDENT                                 { evar ($1) }
  | LIDENT tparguments                     { eapp ($1, $2) }
  | EQUAL OPEN tpexpr COMMA tpexpr CLOSE   { eapp ("=", [$3; $5]) }
  | tpexpr EQSYM tpexpr                    { eapp ("=", [$1; $3]) }
  | tpexpr NEQSYM tpexpr                   { enot (eapp ("=", [$1; $3])) }
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
  | tpatom %prec lowest            { $1 }
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
  | UIDENT COMMA tpvar_list        { evar $1 :: $3 }
  | UIDENT                         { [evar $1] }
;


/* Focal Syntax */

coqfile:
  | BEGINPROOF coqexpr coq_hyp_def_list ENDPROOF EOF
      { ($1, Hyp ("_Zgoal", enot $2, 0) :: $3) }
  | coqexpr coq_hyp_def_list EOF
      { ("theorem", Hyp ("_Zgoal", enot $1, 0) :: $2) }
;
coqexpr:
  | FORALL coqbindings COMMA_ coqexpr
      { mk_coq_all $2 $4 }
  | EXISTS coqbindings COMMA_ coqexpr
      { mk_coq_ex $2 $4 }

  | LET IDENT COLON_EQ_ coqexpr IN coqexpr
      { mk_coq_let $2 $4 $6 }

  | coqexpr DASH_GT_ coqexpr
      { eimply ($1, $3) }

  | coqexpr LT_DASH_GT_ coqexpr
      { eequiv ($1, $3) }

  | coqexpr BACKSL_SLASH_ coqexpr
      { eor ($1, $3) }

  | coqexpr SLASH_BACKSL_ coqexpr
      { eand ($1, $3) }

  | coqexpr EQ_ coqexpr
      { eapp ("=", [$1; $3]) }
  | coqexpr LT_GT_ coqexpr
      { enot (eapp ("=", [$1; $3])) }

  | TILDE_ coqexpr
      { enot ($2) }

  | coqexpr1 coqexpr1_list  %prec apply
      { mk_coq_apply ($1, $2) }

  | coqexpr1
      { $1 }
;

coqexpr1:
  | IDENT
      { evar ($1) }
  | LPAREN_ coqexpr RPAREN_
      { $2 }
;

coqexpr1_list:
  | coqexpr1                  { [$1] }
  | coqexpr1 coqexpr1_list    { $1 :: $2 }
;

coqbindings:
  | coqsimplebinding          { $1 }
  | coqbinding_list           { $1 }
;

coqsimplebinding:
  | coqidlist COLON_ coqtype  { List.map (fun v -> (v, $3)) $1 }
;

coqidlist:
  | /* empty */               { [] }
  | IDENT coqidlist           { $1 :: $2 }
;

coqbinding_list:
  | /* empty */
      { [] }
  | IDENT coqbinding_list
      { ($1, "_") :: $2 }
  | LPAREN_ coqsimplebinding RPAREN_ coqbinding_list
      { $2 @ $4 }
;

coqtype:
  | coqexpr               { mk_type_string $1 }
;

/* normal identifier or unparsed coq expression */
id_or_coqexpr:
  | IDENT  { $1 }
  | STRING { $1 }
;

coqparam_expr:
  | coqexpr
      { ([], $1) }
  | FUN LPAREN_ IDENT COLON_ coqtype RPAREN_ EQ_GT_ coqparam_expr
      { let (params, expr) = $8 in ((evar $3) :: params, expr) }
;

parameter:
  | PARAMETER id_or_coqexpr COLON_ coqexpr PERIOD_
      { $2, Hyp ($2, $4, 1) }

definition:
  | DEFINITION id_or_coqexpr COLON_EQ_ coqparam_expr PERIOD_
      { let (params, expr) = $4 in $2, Def (DefReal ($2, params, expr)) }

coq_hyp_def:
  | DEPENDS ON parameter 
      { let (name, hyp) = $3 in 
          Watch.watch_hyp name;
          hyp
      }
  | DEPENDS ON definition
      { let (name, hyp) = $3 in
          Watch.watch_def name;
          hyp
      }
  | parameter  { snd $1 }
  | definition { snd $1 }
;

coq_hyp_def_list:
  | coq_hyp_def coq_hyp_def_list   { $1 :: $2 }
  | /* empty */                    { [] }
;

%%
