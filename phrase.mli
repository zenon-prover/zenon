(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.7 2006-02-06 17:56:06 doligez Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
  | Sig of string * string list * string  (* sym, args, result *)
  | Inductive of string * string list
;;

val is_def: expr list -> expr -> bool
val make_def: expr * int -> expr list -> expr -> definition

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
  | Annotation of string
;;
