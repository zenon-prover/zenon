(*  Copyright 1997 INRIA  *)
(*  $Id: prove.mli,v 1.3 2009-08-05 14:47:43 doligez Exp $  *)

exception NoProof;;
exception LimitsExceeded;;

val prove : Expr.definition list -> (Expr.expr * int) list -> Mlproof.proof;;
