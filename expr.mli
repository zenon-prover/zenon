(*  Copyright 2003 INRIA  *)
(*  $Id: expr.mli,v 1.3 2004-05-24 13:47:55 delahaye Exp $  *)

(* the [int] argument to the constructors is the hash value *)

type expr = private
  | Evar of string * int
  | Emeta of expr * int
  | Eapp of string * expr list * int

  | Enot of expr * int
  | Eand of expr * expr * int
  | Eor of expr * expr * int
  | Eimply of expr * expr * int
  | Eequiv of expr * expr * int
  | Etrue
  | Efalse

  | Eall of string * string * expr * int
  | Eex of string * string * expr * int
  | Etau of string * string * expr * int
;;

type definition =
  | DefReal of string * string list * expr
  | DefPseudo of (expr * int) * string * string list * expr
;;

type t = expr;;

val equal : t -> t -> bool;;
val hash : t -> int;;

val evar : string -> expr;;
val emeta : expr -> expr;;
val eapp : string * expr list -> expr;;

val enot : expr -> expr;;
val eand : expr * expr -> expr;;
val eor : expr * expr -> expr;;
val eimply : expr * expr -> expr;;
val eequiv : expr * expr -> expr;;
val etrue : expr;;
val efalse : expr;;
val eall : string * string * expr -> expr;;
val eex : string * string * expr -> expr;;
val etau : string * string * expr -> expr;;

val preunifiable : expr -> expr -> bool;;
(* [filters e1 e2]
   Returns true if e1 and e2 are pre-unifiable.
   Assumes that e1 and e2 are terms (i.e. don't have logical connectives
   except inside a tau).
*)

val preunify : expr -> expr -> (expr * expr) list;;
(* [get_filters e1 e2]
   If e1 and e2 are non-trivially pre-unifiable, return the set
   of pre-unifiers.
   Return an empty list if they are not pre-unifiable.
*)

val occurs : expr -> expr -> bool;;
(* [occurs e1 e2] returns true if e1 occurs in e2 *)

val size : expr -> int;;

val substitute : (string * expr) list -> expr -> expr;;

val has_meta : expr -> bool;;

val free_var : expr -> string list
val type_list : expr -> string list
