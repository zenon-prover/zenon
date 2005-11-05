(*  Copyright 2004 INRIA  *)
Version.add "$Id: llproof.ml,v 1.7 2005-11-05 11:13:17 doligez Exp $";;

open Expr;;

type binop =
  | And
  | Or
  | Imply
  | Equiv
;;

type rule =
  | Rfalse
  | Rnottrue
  | Raxiom of expr
  | Rcut of expr
  | Rnoteq of expr
  | Rnotnot of expr
  | Rconnect of binop * expr * expr
  | Rnotconnect of binop * expr * expr
  | Rex of expr * string
  | Rall of expr * expr
  | Rnotex of expr * expr
  | Rnotall of expr * string
  | Rpnotp of expr * expr
  | Rnotequal of expr * expr
  | Rdefinition of expr * expr
  | Rextension of string * expr list * expr list * expr list list
  | Rlemma of string * string list
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;                    (* nom du lemme *)
  params : (string * string) list;  (* parametres, avec leurs types *)
  proof : prooftree;                (* preuve *)
};;

type proof = lemma list;;

let (@@) = List.rev_append;;

let rec direct_close l =
  match l with
  | [] -> raise Not_found
  | h::t ->
      begin match h with
      | Efalse -> { conc = [h]; rule = Rfalse; hyps = [] }
      | Enot (Etrue, _) -> { conc = [h]; rule = Rnottrue; hyps = [] }
      | Enot (Eapp ("=", [a; b], _), _) when Expr.equal a b ->
        { conc = [h]; rule = Rnoteq (a); hyps = [] }
      | Enot (nh, _) ->
          if List.exists (Expr.equal nh) t then
            { conc = [h; nh]; rule = Raxiom (nh); hyps = [] }
          else
            direct_close t
      | _ ->
          let nh = enot h in
          if List.exists (Expr.equal nh) t then
            { conc = [h; nh]; rule = Raxiom (h); hyps = [] }
          else
            direct_close t
      end
;;

let subsumes super sub =
  List.for_all (fun x -> List.exists (Expr.equal x) super) sub.conc
;;

let lemmas = (Hashtbl.create 997 : (string, expr list) Hashtbl.t);;
let init_lemmas ls =
  Hashtbl.clear lemmas;
  List.iter (fun l -> Hashtbl.add lemmas l.name l.proof.conc) ls
;;

let get_lemma_conc name =
  try Hashtbl.find lemmas name
  with Not_found -> assert false
;;

let reduce conc rule hyps =
  let eliminated =
    match rule with
    | Rfalse -> [efalse]
    | Rnottrue -> [enot (etrue)]
    | Raxiom (p) -> [p; enot p]
    | Rcut (p) -> []
    | Rnoteq (a) -> [enot (eapp ("=", [a; a]))]
    | Rnotnot (p) -> [enot (enot (p))]
    | Rconnect (And, p, q) -> [eand (p, q)]
    | Rconnect (Or, p, q) -> [eor (p, q)]
    | Rconnect (Imply, p, q) -> [eimply (p, q)]
    | Rconnect (Equiv, p, q) -> [eequiv (p, q)]
    | Rnotconnect (And, p, q) -> [enot (eand (p, q))]
    | Rnotconnect (Or, p, q) -> [enot (eor (p, q))]
    | Rnotconnect (Imply, p, q) -> [enot (eimply (p, q))]
    | Rnotconnect (Equiv, p, q) -> [enot (eequiv (p, q))]
    | Rex (ep, v) -> [ep]
    | Rall (ap, t) -> [ap]
    | Rnotex (ep, t) -> [enot (ep)]
    | Rnotall (ap, v) -> [enot (ap)]
    | Rpnotp (p, q) -> [p; q]
    | Rnotequal (a, b) -> [enot (eapp ("=", [a; b]))]
    | Rdefinition (fld, unf) -> [fld]
    | Rextension (name, args, cons, hyps) -> cons
    | Rlemma (name, args) -> get_lemma_conc name
  in
  let useful = List.fold_left (fun accu h -> h.conc @@ accu) eliminated hyps in
  List.filter (fun x -> List.exists (Expr.equal x) useful) conc
;;

let rec opt t =
  if t.hyps = [] then t else
  let nhyps = List.map opt t.hyps in
  try direct_close t.conc
  with Not_found ->
  let nconc = reduce t.conc t.rule nhyps in
  try List.find (subsumes nconc) nhyps
  with Not_found ->
  { t with conc = nconc; hyps = nhyps }
;;

let optimise p =
  init_lemmas p;
  List.map (fun x -> {x with proof = opt x.proof}) p
;;
