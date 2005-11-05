(*  Copyright 2004 INRIA  *)
(*  $Id: step.mli,v 1.3 2005-11-05 11:13:17 doligez Exp $  *)

val forms : string -> Expr.expr list -> unit;;
val rule : string -> Mlproof.rule -> unit;;
