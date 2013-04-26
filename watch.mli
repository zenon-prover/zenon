(*  Copyright 2005 INRIA  *)
(*  $Id: watch.mli,v 1.5 2006-02-27 16:56:52 doligez Exp $  *)

val warn :
  (Phrase.phrase * bool) list -> Llproof.proof Lazy.t -> string list -> unit
;;
val warn_unused_var : (Phrase.phrase * bool) list -> unit;;
