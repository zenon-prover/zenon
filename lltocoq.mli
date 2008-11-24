(*  Copyright 2004 INRIA  *)
(*  $Id: lltocoq.mli,v 1.8 2008-11-24 15:28:27 doligez Exp $  *)

val output :
  out_channel ->
  Phrase.phrase list ->
  Phrase.phrase list ->
  Llproof.proof ->
    string list
;;
