(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.3 2004-05-27 17:21:24 doligez Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
;;

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
;;
