(*  Copyright 2005 INRIA  *)
(*  $Id: watch.mli,v 1.4 2005-11-13 22:49:11 doligez Exp $  *)

val warn : Phrase.phrase list -> Llproof.proof Lazy.t -> unit;;
val warn_unused_var : (Phrase.phrase * bool) list -> unit;;
