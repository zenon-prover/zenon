(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.6 2005-11-13 22:49:11 doligez Exp $  *)

val index : int -> 'a -> 'a list -> int;;
val ( @@ ) : 'a list -> 'a list -> 'a list;;
val list_init : int -> (unit -> 'a) -> 'a list;;
val list_last : 'a list -> 'a;;
val occurs : string -> string -> bool;;
val isalnum : char -> bool;;
val debug : ('a, out_channel, unit) format -> 'a;;
