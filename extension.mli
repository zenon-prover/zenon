(*  Copyright 2004 INRIA  *)
(* $Id: extension.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $ *)

type t = {
  name : string;
  newnodes : Expr.expr -> Prio.t -> Node.node list * bool;
  add_formula : Expr.expr -> Prio.t -> unit;
  remove_formula : Expr.expr -> unit;
  to_llproof : Mlproof.proof -> Llproof.prooftree array -> Llproof.prooftree;
};;

val register : t -> unit;;
val activate : string -> unit;;

val newnodes : Expr.expr -> Prio.t -> Node.node list * bool;;
val add_formula : Expr.expr -> Prio.t -> unit;;
val remove_formula : Expr.expr -> unit;;
val to_llproof : Mlproof.proof -> Llproof.prooftree array -> Llproof.prooftree;;
