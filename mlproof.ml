(*  Copyright 2004 INRIA  *)
Version.add "$Id: mlproof.ml,v 1.5 2004-09-28 13:12:58 doligez Exp $";;

open Expr;;
open Printf;;

type side = L | R;;

type rule =
  | Close of expr
  | Close_refl of string * expr
  | Close_sym of string * expr * expr
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
  | P_NotP of expr * expr
  | P_NotP_sym of string * expr * expr
  | NotEqual of expr * expr
  | Definition of definition * expr * expr

  | ConjTree of expr            (* p1/\p2/\...  /  p1, p2, ... *)
  | DisjTree of expr            (* p1\/p2\/...  /  p1 | p2 | ... *)
  | AllPartial of expr * string * int
                                (* Ax.p(x)  /  Axyz.p(s(xyz)) *)
  | NotExPartial of expr * string * int
                                (* -Ex.p(x)  /  -Exyz.p(s(xyz)) *)
  | Refl of string * expr * expr
  | Trans of side * bool * expr * expr

  | Cut of expr                 (*   / p | -p  *)

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

let make_node conc rule hyps subs =
  let remove_hyp hyp sub = diff sub.mlconc hyp in
  let extras = List.map2 remove_hyp hyps subs in
  let extra = List.flatten extras in
  {
    mlconc = union conc extra;
    mlrule = rule;
    mlhyps = Array.of_list subs;
    mlrefc = 1;
  }
;;
