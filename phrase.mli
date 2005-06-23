(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.4 2005-06-23 07:07:59 prevosto Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
;;

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
  | Annotation of string
;;
