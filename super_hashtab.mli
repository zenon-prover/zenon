(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
(*  $Id$  *)

val rules :  ((Expr.expr, string*(Expr.expr list list)) Hashtbl.t);;
module HE :
  sig
    type key = Expr.t
    type 'a t = 'a Hashtbl.Make(Expr).t
    val create : int -> 'a t
    val clear : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
  end
val allforms : int HE.t

val member_he : HE.key -> bool
val add_he : HE.key -> int -> unit
val remove_he : HE.key -> unit
val clear_he :  unit ->unit
val get_all_he : unit -> (HE.key * int) list

val newnodes_mg : Expr.expr list ref
