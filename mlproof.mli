(*  Copyright 2003 INRIA  *)
(*  $Id: mlproof.mli,v 1.4 2004-09-09 15:25:35 doligez Exp $  *)

open Expr;;

type side = L | R;;

type rule =
  | Close of expr               (* p, -p  /  (.)        *)
  | Close_refl of string * expr (* -R(e,e)/  (.)        *)
  | Close_sym of string * expr * expr
                                (* R(e1,e2), -R(e2,e1)  /  (.)      *)
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
  | P_NotP of expr * expr       (* P(a0, ..., an), -P(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn     *)
  | P_NotP_sym of string * expr * expr
                                (* P(a,b), -P(c,d)  /  b!=c  |  a!=d *)
  | NotEqual of expr * expr     (* F(a0, ..., an)!=F(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn     *)

  | Definition of definition * expr * expr
                                (* folded / unfolded              *)

  | ConjTree of expr            (* p1/\p2/\...  /  p1, p2, ...    *)
  | DisjTree of expr            (* p1\/p2\/...  /  p1 | p2 | ...  *)
  | AllPartial of expr * expr   (* A.p  /  A.(\x.p(f(x)))         *)
  | NotExPartial of expr * expr (* -E.p  /  -E.(\x.p(f(x)))       *)
  | Refl of string * expr * expr (* -P(a,b)  /  a!=b *)
  | Trans of side * bool * expr * expr
    (* Trans (side, sym, e1, e2):
        side = L, sym = false:    -P(a,b) p(c,d)  /  c!=a | -P(d,b)
        side = R, sym = false:    -P(a,b) p(c,d)  /  d!=b | -P(a,c)
        side = L, sym = true:     -P(a,b) p(c,d)  /  c!=b | -P(a,d)
        side = R, sym = true:     -P(a,b) p(c,d)  /  d!=a | -P(c,b)
      In all these, p may be either P or =
    *)

  | Cut of expr                 (*   / p | -p  *)

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
val make_node :
   Expr.expr list -> rule -> Expr.expr list -> proof list -> proof
;;
