(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.3 2004-10-15 11:55:03 doligez Exp $ *)

val produce_proof :
  Phrase.phrase list -> bool -> string option -> bool -> Llproof.proof -> int
;;
