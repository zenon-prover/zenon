(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.3.2.1 2005-10-26 16:12:39 doligez Exp $ *)

val produce_proof :
  out_channel -> Phrase.phrase list -> Llproof.proof -> unit
;;
