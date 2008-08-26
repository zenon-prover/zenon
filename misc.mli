(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.8 2008-08-26 13:47:41 doligez Exp $  *)

val index : int -> 'a -> 'a list -> int;;
val ( @@ ) : 'a list -> 'a list -> 'a list;;
val list_init : int -> (unit -> 'a) -> 'a list;;
val list_last : 'a list -> 'a;;
val list_iteri : (int -> 'a -> unit) -> 'a list -> unit;;
val list_iter3 :
  ('a -> 'b -> 'c -> unit) -> 'a list -> 'b list -> 'c list -> unit
;;
val occurs : string -> string -> bool;;
val isalnum : char -> bool;;
val debug : ('a, out_channel, unit) format -> 'a;;
