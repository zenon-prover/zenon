(*  Copyright 2004 INRIA  *)
(*  $Id: step.mli,v 1.2.2.1 2005-10-03 10:22:30 doligez Exp $  *)

val forms : string -> Expr.expr list -> unit;;
val rule : string -> Mlproof.rule -> unit;;
