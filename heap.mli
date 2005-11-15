(*  Copyright 2001 INRIA  *)
(*  $Id: heap.mli,v 1.3 2005-11-15 15:02:26 doligez Exp $  *)

type 'a t;;

val empty : ('a -> 'a -> int) -> 'a t;;
val insert : 'a t -> 'a -> 'a t;;
val remove : 'a t -> ('a * 'a t) option;;
val head : 'a t -> 'a option;;
val length : 'a t -> int;;
val is_empty : 'a t -> bool;;
val iter : ('a -> unit) -> 'a t -> unit;;
