(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.5 2006-02-16 09:22:46 doligez Exp $ *)

val output : out_channel -> Phrase.phrase list -> Llproof.proof -> unit;;
