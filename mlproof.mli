(*  Copyright 2003 INRIA  *)
(* $Id: mlproof.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $ *)

open Expr;;

type rule =
  | Close1 of expr              (* e!=e   /  (.)        *)
  | Close2 of expr              (* p, -p  /  (.)        *)
  | False                       (* false  /  (.)        *)
  | NotTrue                     (* -true  /  (.)        *)
  | NotNot of expr              (* --p    /  p          *)
  | And of expr * expr          (* p/\q   /  p, q       *)
  | NotOr of expr * expr        (* -(p\/q)  /  -p, -q   *)
  | NotImpl of expr * expr      (* -(p=>q)  /  p, -q    *)
  | NotAll of expr              (* -A.p  /  -p(t(~p))   (expr = -A.p)  *)
  | Ex of expr                  (* E.p  /  p(t(p))      (expr = E.p)   *)
  | All of expr * expr          (* A.p  /  p(e)         (expr1 = A.p)  *)
  | NotEx of expr * expr        (* -E.p  /  -p(e)       (expr1 = -E.p) *)
  | Or of expr * expr           (* p\/q  /  p | q       *)
  | Impl of expr * expr         (* p=>q  /  -p | q      *)
  | NotAnd of expr * expr       (* -(p/\q)  /  -p | -q  *)
  | Equiv of expr * expr        (* p<=>q  /  -p, -q | p, q    *)
  | NotEquiv of expr * expr     (* -(p<=>q)  /  -p, q | p, -q *)
  | Equal_NotEqual of expr * expr * expr * expr
                                (* a=b, c!=d  /  c!=a, c!=b | a!=d, b!=d *)
  | P_NotP of expr * expr       (* P(a0, ..., an), -P(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn     *)
  | NotEqual of expr * expr     (* F(a0, ..., an)!=F(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn     *)

  | Definition of definition * expr
                                (* expr / unfolded                *)

  | ConjTree of expr            (* p1/\p2/\...  /  p1, p2, ...    *)
  | DisjTree of expr            (* p1\/p2\/...  /  p1 | p2 | ...  *)
  | AllPartial of expr * expr   (* A.p  /  A.(\x.p(f(x)))         *)
  | NotExPartial of expr * expr (* -E.p  /  -E.(\x.p(f(x)))       *)
  | CloseEq of expr * expr      (* e1 = e2, e2 != e1  /  (.)      *)

  | Ext of string * string * expr list
                                (* extension, rule, arguments *)
;;

type proof = {
  mlconc : expr list;      (* conclusion *)
  mlrule : rule;           (* rule *)
  mlhyps : proof array;    (* proof branches *)
  mutable mlrefc : int;    (* reference count *)
};;

val size : proof -> int;;
