(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.6 2005-11-05 11:13:17 doligez Exp $  *)

type coqterm;;
type coqproof;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;
val print : out_channel -> coqproof -> unit;;

val declare_context : out_channel -> Phrase.phrase list -> unit;;
val synthesize : string -> string;;
