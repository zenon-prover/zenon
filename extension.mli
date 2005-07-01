(*  Copyright 2004 INRIA  *)
(*  $Id: extension.mli,v 1.5 2005-07-01 12:24:47 prevosto Exp $  *)

type translator =
    (Expr.expr -> Expr.expr) -> (Expr.expr -> Expr.expr)
    -> Mlproof.proof -> (Llproof.prooftree * Expr.expr list) array
    -> Llproof.prooftree * Expr.expr list
;;

type t = {
  name : string;
  newnodes : int -> Expr.expr -> Node.node_item list Lazy.t;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  to_llproof : translator;
};;

val register : t -> unit;;
val activate : string -> unit;;

val is_enabled: string -> bool

val newnodes : int -> Expr.expr -> Node.node_item list Lazy.t list;;
val add_formula : Expr.expr -> unit;;
val remove_formula : Expr.expr -> unit;;
val to_llproof : translator;;
