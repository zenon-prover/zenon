(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.2 2004-05-27 17:21:24 doligez Exp $  *)

type coqterm;;

val trproof : Phrase.phrase list -> Llproof.proof -> coqterm;;

module V8 : sig
  val print : string option -> coqterm -> unit;;
end;;

module V7 : sig
  val print : string option -> coqterm -> unit;;
end;;
