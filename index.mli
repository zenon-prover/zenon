(*  Copyright 2004 INRIA  *)
(*  $Id: index.mli,v 1.2 2004-05-28 11:29:35 doligez Exp $  *)

open Expr;;

(* ==== main formula list ==== *)

(* [add] and [remove] must be used in LIFO order *)
val add : expr -> Prio.t -> unit;;
val remove : expr -> unit;;

val member : expr -> bool;;
val get_prio : expr -> Prio.t;;

val find_pos : string -> expr list;;
val find_neg : string -> expr list;;
val find_equal : expr -> expr list;;
val find_noteq : expr -> expr list;;

val find_rewrite : expr -> (expr * expr) list;;
(* same as find_equal, but return only oriented equations *)

(* ==== proof cache ==== *)

val add_proof : Mlproof.proof -> unit;;
val search_proof : unit -> Mlproof.proof option;;

(* ==== definitions ==== *)

val add_def : definition -> unit;;
val has_def : string -> bool;;
val get_def : string -> definition * string list * expr;;

(* ==== depth of metavariables ==== *)

val add_meta : expr -> int -> unit;;
val remove_meta : expr -> unit;;
val get_meta : expr -> int;;

(* ==== number of nodes in the heap made redundant by a formula ==== *)

val add_branches : expr list array -> unit;;
val remove_branches : expr list array -> unit;;
val get_branches : expr list -> int;;

(* ==== numbering for formulas ==== *)

val get_number : expr -> int;;
val get_formula : int -> expr (* raises Not_found *);;
