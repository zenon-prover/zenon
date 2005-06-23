(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.5 2005-06-23 13:05:47 prevosto Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
;;

val is_def: expr list -> expr -> bool
val make_def: expr * int -> expr list -> expr -> definition

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
  | Annotation of string
;;
