(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.2 2004-04-29 13:04:52 doligez Exp $  *)

open Expr;;

type phrase =
  | Hyp of expr * int
  | Def of definition
;;

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Clause of string * string * expr list
  | Formula of string * string * expr
;;
