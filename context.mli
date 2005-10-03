(*  Copyright 2005 INRIA  *)
(*  $Id: context.mli,v 1.1.2.1 2005-10-03 10:22:30 doligez Exp $  *)

val get_meta_types : Llproof.proof -> (string * string) list;;

val declare_coq_context : out_channel -> Phrase.phrase list -> unit;;
