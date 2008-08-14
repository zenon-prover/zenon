(*  Copyright 2004 INRIA  *)
(*  $Id: phrase.mli,v 1.9 2008-08-14 14:02:09 doligez Exp $  *)

open Expr;;

type phrase =
  | Hyp of string * expr * int
  | Def of definition
  | Sig of string * string list * string  (* sym, args, result *)
  | Inductive of string * (string * string list) list
;;

val separate : phrase list -> definition list * (expr * int) list;;

type tpphrase =
  | Include of string
  | Formula of string * string * expr
  | Annotation of string
;;

val change_to_def : expr -> definition;;
(** Turn a def-shaped formula into a (real) definition.
    Raise [Invalid_argument] if the argument is not def-shaped. *)
