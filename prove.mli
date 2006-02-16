(*  Copyright 1997 INRIA  *)
(*  $Id: prove.mli,v 1.2 2006-02-16 09:22:46 doligez Exp $  *)

exception NoProof;;

val prove : Expr.definition list -> (Expr.expr * int) list -> Mlproof.proof;;
