(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.5 2004-11-19 15:07:39 doligez Exp $  *)

type coqterm;;

type coqproof = (string * coqterm) list * string * coqterm;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;

val print : string option -> coqproof -> unit;;
