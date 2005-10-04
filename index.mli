(*  Copyright 2004 INRIA  *)
(*  $Id: index.mli,v 1.3.2.2 2005-10-04 15:57:04 doligez Exp $  *)

open Expr;;

(* ==== main formula list ==== *)

(* [add] and [remove] must be used in LIFO order *)
val add : expr -> int -> unit;;
val remove : expr -> unit;;

val member : expr -> bool;;
val get_goalness : expr -> int;;
val get_all : unit -> expr list;;

val find_pos : string -> expr list;;
val find_neg : string -> expr list;;

(* ==== transitive relations ==== *)

type direction = Left | Right | Both;;

type head = Sym of string | Tau of expr | Wild;;
val get_head : expr -> head;;

val add_trans : expr -> direction -> unit;;
val find_trans_left : string -> head -> expr list;;
val find_trans_right : string -> head -> expr list;;

val find_trans_leftonly : string -> head -> expr list;;
val find_trans_rightonly : string -> head -> expr list;;

val add_negtrans : expr -> unit;;
val find_negtrans_left : string -> head -> expr list;;
val find_negtrans_right : string -> head -> expr list;;

val find_all_negtrans_left : head -> expr list;;
val find_all_negtrans_right : head -> expr list;;

(* ==== proof cache ==== *)

val add_proof : Mlproof.proof -> unit;;
val search_proof : unit -> Mlproof.proof option;;

(* ==== definitions ==== *)

val add_def : definition -> unit;;
val has_def : string -> bool;;
val get_def : string -> definition * expr list * expr;;

(* ==== depth of metavariables ==== *)

val add_meta : expr -> int -> unit;;
val remove_meta : expr -> unit;;
val get_meta : expr -> int;;

(* ==== numbering for formulas ==== *)

val get_number : expr -> int;;
val get_formula : int -> expr (* raises Not_found *);;
