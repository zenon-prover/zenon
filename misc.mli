(*  Copyright 1997 INRIA  *)
(*  $Id: misc.mli,v 1.13 2008-11-18 12:33:29 doligez Exp $  *)

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

val string_split : string -> string list;;
val occurs : string -> string -> bool;;
val replace_first : string -> string -> string -> string;;
val isalnum : char -> bool;;

val debug : ('a, out_channel, unit) format -> 'a;;

val base36 : int -> string;;
val base26 : int -> string;;
