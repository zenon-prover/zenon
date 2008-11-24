(*  Copyright 2008 INRIA  *)
(*  $Id: lltoisar.mli,v 1.2 2008-11-24 15:28:27 doligez Exp $  *)

val output :
  out_channel ->
  Phrase.phrase list ->
  Phrase.phrase list ->
  Llproof.proof ->
  string list
;;
