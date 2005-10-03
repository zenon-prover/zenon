(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.3.2.1 2005-10-03 10:22:30 doligez Exp $  *)

val index : int -> 'a -> 'a list -> int;;
val ( @@ ) : 'a list -> 'a list -> 'a list;;
val occurs : string -> string -> bool;;
val list_init : int -> (unit -> 'a) -> 'a list;;
