(*  Copyright 2001 INRIA  *)
(*  $Id: heap.mli,v 1.2 2004-04-29 13:04:52 doligez Exp $  *)

type 'a t;;

val empty : ('a -> 'a -> int) -> 'a t;;
val insert : 'a t -> 'a -> 'a t;;
val remove : 'a t -> ('a * 'a t) option;;
val head : 'a t -> 'a option;;
val length : 'a t -> int;;
val iter : ('a -> unit) -> 'a t -> unit;;
