(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.5.2.1 2005-10-03 10:22:30 doligez Exp $  *)

type coqterm;;

type coqproof;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;

val declare_context : out_channel -> Phrase.phrase list -> unit;;

val print : string option -> coqproof -> unit;;
