(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.4 2004-06-21 19:37:42 doligez Exp $  *)

type coqterm;;

type coqproof = (string * coqterm) list * string * coqterm;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqproof;;

module V8 : sig
  val print : string option -> coqproof -> unit;;
end;;

module V7 : sig
  val print : string option -> coqproof -> unit;;
end;;
