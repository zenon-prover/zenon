(*  Copyright 2004 INRIA  *)
(*  $Id: coqterm.mli,v 1.1 2004-05-26 16:23:52 doligez Exp $  *)

type coqterm;;

val print : string option -> coqterm -> unit;;
val trproof : Llproof.proof -> coqterm;;
