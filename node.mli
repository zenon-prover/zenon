(*  Copyright 2004 INRIA  *)
(*  $Id: node.mli,v 1.3 2004-09-09 15:25:35 doligez Exp $  *)

type node = {
  nconc : Expr.expr list;
  nrule : Mlproof.rule;
  nprio : Prio.t;
  nbranches : Expr.expr list array;
};;

type node_item =
  | Node of node
  | Stop
;;

val relevant : node_item list Lazy.t list -> node list;;
(* Evaluate until the Stop; there must be a Stop. *)

