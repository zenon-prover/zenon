(*  Copyright 2004 INRIA  *)
(*  $Id: eqrel.mli,v 1.2 2004-09-09 15:25:35 doligez Exp $  *)

val analyse : Expr.expr -> unit;;

val refl : string -> bool;;
val sym : string -> bool;;
val trans : string -> bool;;
val any : string -> bool;;

val get_refl_hyp : string -> Expr.expr;;
val get_sym_hyp : string -> Expr.expr;;
val get_trans_hyp : string -> Expr.expr;;

val get_proof : Expr.expr -> Mlproof.proof * Expr.expr list;;

val print_rels : out_channel -> unit;;
