(*  Copyright 2004 INRIA  *)
(*  $Id: mltoll.mli,v 1.5 2005-11-05 11:13:17 doligez Exp $  *)

val translate : string -> Phrase.phrase list -> Mlproof.proof -> Llproof.proof;;

val is_meta : string -> bool;;
val get_meta_type : string -> string;;
