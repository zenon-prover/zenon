(*  Copyright 2004 INRIA  *)
(*  $Id: eqrel.mli,v 1.1 2004-06-04 09:29:15 doligez Exp $  *)

val analyse : Expr.expr -> unit;;

val refl : string -> bool;;
val sym : string -> bool;;
val trans : string -> bool;;

val print_rels : out_channel -> unit;;
