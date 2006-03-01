(*  Copyright 2004 INRIA  *)
(*  $Id: lltocoq.mli,v 1.7 2006-03-01 14:39:03 doligez Exp $  *)

val output : out_channel -> Phrase.phrase list -> Llproof.proof -> string list;;
