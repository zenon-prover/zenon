(*  Copyright 2004 INRIA  *)
(*  $Id: extension.mli,v 1.3 2004-05-27 17:21:24 doligez Exp $  *)

type translator =
    (Expr.expr -> Expr.expr) -> (Expr.expr -> Expr.expr)
    -> Mlproof.proof -> Llproof.prooftree array -> Llproof.prooftree
;;

type t = {
  name : string;
  newnodes : Expr.expr -> Prio.t -> Node.node list * bool;
  add_formula : Expr.expr -> Prio.t -> unit;
  remove_formula : Expr.expr -> unit;
  to_llproof : translator;
};;

val register : t -> unit;;
val activate : string -> unit;;

val newnodes : Expr.expr -> Prio.t -> Node.node list * bool;;
val add_formula : Expr.expr -> Prio.t -> unit;;
val remove_formula : Expr.expr -> unit;;
val to_llproof : translator;;
