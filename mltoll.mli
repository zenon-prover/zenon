(*  Copyright 2004 INRIA  *)
(*  $Id: mltoll.mli,v 1.4 2004-09-09 15:25:35 doligez Exp $  *)

val translate : string -> Phrase.phrase list -> Mlproof.proof -> Llproof.proof;;
