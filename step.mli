(*  Copyright 2004 INRIA  *)
(*  $Id: step.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $  *)

val forms : string -> (Expr.expr * Prio.t) list -> unit;;
val rule : string -> Mlproof.rule -> unit;;
