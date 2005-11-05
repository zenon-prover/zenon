(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.4 2005-11-05 11:13:17 doligez Exp $  *)

val index : int -> 'a -> 'a list -> int;;
val ( @@ ) : 'a list -> 'a list -> 'a list;;
val occurs : string -> string -> bool;;
val list_init : int -> (unit -> 'a) -> 'a list;;
val isalnum : char -> bool;;
