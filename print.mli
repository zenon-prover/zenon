(*  Copyright 2004 INRIA  *)
(*  $Id: print.mli,v 1.2 2004-04-29 13:04:52 doligez Exp $  *)

val expr : Expr.expr -> unit;;
val expr_soft : Expr.expr -> unit;;

val phrase : Phrase.phrase -> unit;;

val hlproof : int -> Mlproof.proof -> unit;;

val mlproof : Mlproof.proof -> unit;;
val mlproof_rule : Mlproof.rule -> unit;;
val mlproof_rule_soft : Mlproof.rule -> unit;;

val llproof : Llproof.proof -> unit;;
