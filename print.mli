(*  Copyright 2004 INRIA  *)
(*  $Id: print.mli,v 1.3 2004-05-24 13:47:55 delahaye Exp $  *)

val set_outc : out_channel -> unit
val get_outc : unit -> out_channel

val expr : Expr.expr -> unit;;
val expr_soft : Expr.expr -> unit;;

val phrase : Phrase.phrase -> unit;;

val hlproof : int -> Mlproof.proof -> unit;;

val mlproof : Mlproof.proof -> unit;;
val mlproof_rule : Mlproof.rule -> unit;;
val mlproof_rule_soft : Mlproof.rule -> unit;;

val llproof : Llproof.proof -> unit;;
