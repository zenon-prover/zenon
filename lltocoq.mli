(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.4 2005-11-05 11:13:17 doligez Exp $ *)

val produce_proof :
  out_channel -> Phrase.phrase list -> Llproof.proof -> unit
;;
