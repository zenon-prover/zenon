(*  Copyright 1997 INRIA  *)
(*  $Id: prove.mli,v 1.1 2004-04-01 11:37:44 doligez Exp $  *)

exception NoProof;;

val prove : Expr.definition list -> (Expr.expr * int) list -> Mlproof.proof;;
