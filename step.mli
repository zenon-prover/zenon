(*  Copyright 2004 INRIA  *)
(*  $Id: step.mli,v 1.4 2005-11-13 22:49:11 doligez Exp $  *)

val forms : string -> (Expr.expr * Expr.goalness) list -> unit;;
val rule : string -> Mlproof.rule -> unit;;
