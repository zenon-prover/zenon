(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.11 2008-11-24 15:28:26 doligez Exp $  *)

type coqterm;;
type coqproof;;

val trproof :
  Phrase.phrase list ->
  Phrase.phrase list ->
  Llproof.proof ->
    coqproof * string list
;;
val print : out_channel -> coqproof -> unit;;

val declare_context : out_channel -> Phrase.phrase list -> unit;;
val print_use_all : out_channel -> Phrase.phrase list -> unit;;

val init_mapping : Phrase.phrase list -> unit;;
val is_mapped : Expr.expr -> bool;;
val is_goal : Expr.expr -> bool;;
val init_inductive : Phrase.phrase list -> unit;;
val get_inductive :
  string -> string list * (string * Phrase.inductive_arg list) list
;;
val getname : Expr.expr -> string;;
val synthesize : string -> string;;
val constants_used : string list ref;;
exception Cannot_infer of string;;
