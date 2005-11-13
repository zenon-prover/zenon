(*  Copyright 2004 INRIA  *)
(*  $Id: node.mli,v 1.5 2005-11-13 22:49:11 doligez Exp $  *)

open Expr;;

type priority =
  | Arity
  | Inst of int
;;

type node = {
  nconc : Expr.expr list;
  nrule : Mlproof.rule;
  nprio : priority;
  ngoal : int;
  nbranches : Expr.expr list array;
};;

type node_item =
  | Node of node
  | Stop
;;

val relevant : node_item list list -> node list * bool;;
(* Flatten the list and cut off at the Stop, if any.
   Return true if there was a stop.
*)

type queue;;
val empty : queue;;
val insert : queue -> node -> queue;;
val remove : queue -> (node * queue) option;;
val head : queue -> node option;;

val size : queue -> string;;  (* for debugging *)
