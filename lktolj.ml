open Printf;;
open Expr;;
open Llproof;;
open Namespace;;

exception Found of expr;;

let lemmas = (Hashtbl.create 997 : (string, lemma) Hashtbl.t);;

let get_lemma name =
  try Hashtbl.find lemmas name
  with Not_found -> assert false
;;

let concls_of_rule rule =
  match rule with
  | Rfalse -> [efalse]
  | Rnottrue -> [enot (etrue)]
  | Raxiom (p) -> [p; enot p]
  | Rcut (p) -> []
  | Rnoteq (a) -> [enot (eapp ("=", [a; a]))]
  | Reqsym (a, b) -> [eapp ("=", [a; b]); enot (eapp ("=", [b; a]))]
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
  | RcongruenceLR (p, a, b) -> [apply p a; eapp ("=", [a; b])]
  | RcongruenceRL (p, a, b) -> [apply p a; eapp ("=", [b; a])]
  | Rdefinition (name, sym, args, body, recarg, fld, unf) -> [fld]
  | Rextension (ext, name, args, cons, hyps) -> cons
  | Rlemma (name, args) -> (get_lemma name).proof.conc
;;

let translate proof = 
  match proof.rule with
  | Rfalse -> proof
  | Rnottrue -> proof
  | Raxiom (p) -> proof
  | Rcut (p) -> proof
  | Rnoteq (a) -> proof
  | Reqsym (a, b) -> proof
  | Rnotnot (p) -> proof
  | Rconnect (And, p, q) -> proof
  | Rconnect (Or, p, q) -> proof
  | Rconnect (Imply, p, q) -> proof
  | Rconnect (Equiv, p, q) -> proof
  | Rnotconnect (And, p, q) -> proof
  | Rnotconnect (Or, p, q) -> proof
  | Rnotconnect (Imply, p, q) -> proof 
  | Rnotconnect (Equiv, p, q) -> proof
  | Rex (ep, v) -> proof
  | Rall (ap, t) -> proof
  | Rnotex (ep, t) -> proof
  | Rnotall (ap, v) -> proof
  | Rpnotp (p, q) -> proof
  | Rnotequal (a, b) -> proof
  | RcongruenceLR (p, a, b) -> proof
  | RcongruenceRL (p, a, b) -> proof
  | Rdefinition (name, sym, args, body, recarg, fld, unf) -> proof
  | Rextension (ext, name, args, cons, hyps) -> proof
  | Rlemma (name, args) -> proof
;;
