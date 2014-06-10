
type t

exception Mismatch of t * t
exception Base_expected
exception Not_enough_args
exception Function_expected

val type_bool : t
val type_int : t
val type_rat : t
val type_real : t

val atomic : string -> t
val mk_poly : string list -> t -> t
val mk_constr : string -> t list -> t
val mk_arrow : t list -> t -> t

val equal : t -> t -> bool
val compare : t -> t -> int

val bool_app : t list -> t
val bool_app_opt : t option list -> t option
val type_eq : t list -> t
val type_app : t -> t list -> t
val type_app_opt : string * t option -> t option list -> t option

val to_string : t -> string

(* TPTP.TFF typing *)
val tff_check : t -> bool

(* Auxiliary function *)
val ksplit : int -> 'a list -> 'a list * 'a list
val find2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a * 'b
