(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.3 2004-06-01 11:56:29 doligez Exp $  *)

type coqterm;;

val trproof : Phrase.phrase list -> Llproof.proof -> string * coqterm;;

module V8 : sig
  val print : string option -> string * coqterm -> unit;;
end;;

module V7 : sig
  val print : string option -> string * coqterm -> unit;;
end;;
