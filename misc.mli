(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.11 2008-10-23 09:01:20 doligez Exp $  *)

val index : int -> 'a -> 'a list -> int;;
val ( @@ ) : 'a list -> 'a list -> 'a list;;
val list_init : int -> (unit -> 'a) -> 'a list;;
val list_last : 'a list -> 'a;;
val list_iteri : (int -> 'a -> unit) -> 'a list -> unit;;
val list_iter3 :
  ('a -> 'b -> 'c -> unit) -> 'a list -> 'b list -> 'c list -> unit
;;
val list_fold_left3 :
  ('accu -> 'a -> 'b -> 'c -> 'accu) -> 'accu -> 'a list -> 'b list -> 'c list
  -> 'accu
;;

val occurs : string -> string -> bool;;
val isalnum : char -> bool;;
val debug : ('a, out_channel, unit) format -> 'a;;

val base36 : int -> string;;
val base26 : int -> string;;
