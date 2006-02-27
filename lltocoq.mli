(*  Copyright 2004 INRIA  *)
(* $Id: lltocoq.mli,v 1.6 2006-02-27 16:56:52 doligez Exp $ *)

val output : out_channel -> Phrase.phrase list -> Llproof.proof -> string list;;
