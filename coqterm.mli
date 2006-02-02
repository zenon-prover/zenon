(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.8 2006-02-02 22:13:54 doligez Exp $  *)

type coqterm;;
type coqproof;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;
val print : out_channel -> coqproof -> unit;;



val declare_context : out_channel -> Phrase.phrase list -> unit;;

val init_mapping : Phrase.phrase list -> unit;;
val is_mapped : Expr.expr -> bool;;
val is_goal : Expr.expr -> bool;;
val getname : Expr.expr -> string;;
val synthesize : string -> string;;
exception Cannot_infer of string;;
