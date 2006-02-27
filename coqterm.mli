(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.9 2006-02-27 16:56:52 doligez Exp $  *)

type coqterm;;
type coqproof;;

val trproof :
  Phrase.phrase list -> Llproof.proof -> coqproof * string list
;;
val print : out_channel -> coqproof -> unit;;


val declare_context : out_channel -> Phrase.phrase list -> unit;;

val init_mapping : Phrase.phrase list -> unit;;
val is_mapped : Expr.expr -> bool;;
val is_goal : Expr.expr -> bool;;
val getname : Expr.expr -> string;;
val synthesize : string -> string;;
val constants_used : string list ref;;
exception Cannot_infer of string;;
