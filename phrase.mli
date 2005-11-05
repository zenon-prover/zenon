(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.6 2005-11-05 11:13:17 doligez Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
  | Sig of string * string list * string  (* sym, args, result *)
;;

val is_def: expr list -> expr -> bool
val make_def: expr * int -> expr list -> expr -> definition

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
  | Annotation of string
;;
