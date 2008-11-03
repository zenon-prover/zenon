(*  Copyright 2004 INRIA  *)
(*  $Id: mltoll.mli,v 1.6 2008-11-03 14:17:25 doligez Exp $  *)

val translate : string -> Phrase.phrase list -> Mlproof.proof -> Llproof.proof;;

val is_meta : string -> bool;;
val get_meta_type : string -> string;;
