(*  Copyright 2004 INRIA  *)
(*  $Id: extension.mli,v 1.8 2005-11-13 22:49:11 doligez Exp $  *)

type translator =
    (Expr.expr -> Expr.expr) -> (Expr.expr -> Expr.expr)
    -> Mlproof.proof -> (Llproof.prooftree * Expr.expr list) array
    -> Llproof.prooftree * Expr.expr list
;;

type t = {
  name : string;
  newnodes : Expr.expr -> Expr.goalness -> Node.node_item list;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  preprocess : Phrase.phrase list -> Phrase.phrase list;
  postprocess : Llproof.proof -> Llproof.proof;
  to_llproof : translator;
  declare_context_coq : out_channel -> string list;
};;

val register : t -> unit;;
val activate : string -> unit;;

val is_active: string -> bool;;

val newnodes : Expr.expr -> Expr.goalness -> Node.node_item list list;;
val add_formula : Expr.expr -> unit;;
val remove_formula : Expr.expr -> unit;;
val preprocess : Phrase.phrase list -> Phrase.phrase list;;
val postprocess : Llproof.proof -> Llproof.proof;;
val to_llproof : translator;;
val declare_context_coq : out_channel -> string list;;
