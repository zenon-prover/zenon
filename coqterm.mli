(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.5.2.2 2005-10-26 16:12:39 doligez Exp $  *)

type coqterm;;

type coqproof;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;

val declare_context : out_channel -> Phrase.phrase list -> unit;;

val print : out_channel -> coqproof -> unit;;
