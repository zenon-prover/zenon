(*  Copyright 2004 INRIA  *)
(*  $Id: step.mli,v 1.2 2004-09-09 15:25:35 doligez Exp $  *)

val forms : string -> (Expr.expr * int) list -> unit;;
val rule : string -> Mlproof.rule -> unit;;
