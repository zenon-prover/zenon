(*  Copyright 2004 INRIA  *)
Version.add "$Id: mlproof.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

open Expr;;
open Printf;;

type rule =
  | Close1 of expr              (* e!=e   /             *)
  | Close2 of expr              (* p, -p  /             *)
  | False                       (* false  /             *)
  | NotTrue                     (* -true  /             *)
  | NotNot of expr              (* --p    /  p          *)
  | And of expr * expr          (* p/\q   /  p, q       *)
  | NotOr of expr * expr        (* -(p\/q)  /  -p, -q   *)
  | NotImpl of expr * expr      (* -(p=>q)  /  p, -q    *)
  | NotAll of expr              (* -A.p  /  -p(t(p))    *)
  | Ex of expr                  (* E.p  /  p(t(p))      *)
  | All of expr * expr          (* A.p  /  p(e)         *)
  | NotEx of expr * expr        (* -E.p  /  -p(e)       *)
  | Or of expr * expr           (* p\/q  /  p | q       *)
  | Impl of expr * expr         (* p=>q  /  -p | q      *)
  | NotAnd of expr * expr       (* -(p/\q)  /  -p | -q  *)
  | Equiv of expr * expr        (* p<=>q  /  -p, -q | p, q *)
  | NotEquiv of expr * expr     (* -(p<=>q)  /  -p, q | p, -q *)
  | Equal_NotEqual of expr * expr * expr * expr
                                (* a=b, c!=d  /  c!=a, c!=b | a!=d, b!=d *)
  | P_NotP of expr * expr       (* P(a0, ..., an), -P(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn *)
  | NotEqual of expr * expr     (* F(a0, ..., an)!=F(b0, ..., bn)
                                      / a0!=b0 | ... | an!=bn *)
  | Definition of definition * expr   (* expr / unfolded *)

  | ConjTree of expr            (* p1/\p2/\...  /  p1, p2, ... *)
  | DisjTree of expr            (* p1\/p2\/...  /  p1 | p2 | ... *)
  | AllPartial of expr * expr   (* A.p  /  A.(\x.p(f(x))) *)
  | NotExPartial of expr * expr (* -E.p  /  -E.(\x.p(f(x))) *)

  | CloseEq of expr * expr      (* e1 = e2, e2 != e1  /  (.)      *)

  | Ext of string * string * expr list
;;

type proof = {
  mlconc : expr list;      (* conclusion *)
  mlrule : rule;           (* rule *)
  mlhyps : proof array;    (* proof branches *)
  mutable mlrefc : int;    (* reference count *)
};;

let rec size p =
  if p.mlrefc < 0 then 0 else begin
    p.mlrefc <- - p.mlrefc;
    1 + Array.fold_left (fun accu pr -> accu + size pr) 0 p.mlhyps
  end
;;
