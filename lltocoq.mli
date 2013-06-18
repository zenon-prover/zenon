(*  Copyright 2004 INRIA  *)
(*  $Id: lltocoq.mli,v 1.9 2011-12-28 16:43:33 doligez Exp $  *)

val output :
  out_channel ->
  Phrase.phrase list ->
  Phrase.phrase list ->
  Llproof.proof ->
    string list
;;

val p_expr : out_channel -> Expr.expr -> unit;;

val p_list : string -> (out_channel -> 'a -> unit) -> string -> out_channel ->
  'a list -> unit;;
val p_expr_list : out_channel -> Expr.expr list  -> unit;;
val p_name_list : out_channel -> Expr.expr list  -> unit;;
val p_intros : out_channel -> Expr.expr list  -> unit;;
