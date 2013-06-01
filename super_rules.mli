(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
(*  $Id$  *)

exception SuperLimitsExceeded;;


val separate :
  Phrase.phrase list ->
  (string * Expr.t* Expr.goalness) list * 
    (string * Expr.t* Expr.goalness) list

val suppr_name : ('a * 'b * int) list -> ('b * int) list

val to_sded :
           (string * Expr.t * Expr.goalness) list -> Mlproof.proof
* (string * Expr.t * Expr.goalness) list
