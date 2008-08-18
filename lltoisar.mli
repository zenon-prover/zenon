(*  Copyright 2008 INRIA  *)
(*  $Id: lltoisar.mli,v 1.1 2008-08-18 09:39:11 doligez Exp $  *)

val output : out_channel -> Phrase.phrase list -> Llproof.proof -> string list;;
