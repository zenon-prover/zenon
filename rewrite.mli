(*  Copyright 2003 INRIA  *)
(*  $Id: modnorm.mli,v 1.00 2013-04_05 15:19:00 halmagrand Exp $  *)

open Expr;;
open Print;;


val rename_aux : expr -> (expr * expr) list -> expr * (expr * expr) list;;
(* [rename e l]
   return [e l] with e the expr with new names of variables
   and l the list of pair with old and new names.
*)

val rename : expr -> expr * (expr * expr) list;;
(* [rename e]
   return [e l] with e the expr with new names of variables
   and l the list of pair with old and new names.
*)

val unif_aux : ( expr * expr ) list -> expr -> expr -> (expr * expr ) list;;
(* [unif_aux l t1 t2]
   return [l] the list of pair whch symbolise the substitution 
   sigma : t1 -> t2
*)

val unif : expr -> expr -> (expr * expr ) list;;
(* [unif t1 t2]
   return [l] the list of pair whch symbolise the substitution 
   sigma : t1 -> t2
*)

val rewrite_term : (expr * expr) -> expr -> expr;;

val rewrite_prop : (expr * expr) -> expr -> expr;;

val normalize_fm : expr -> expr;;

val normalize_list : expr list -> expr list;;


val print_list_expr : expr list -> unit;;
val printer : expr -> unit;;

exception Unif_failed;;
