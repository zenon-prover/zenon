
exception Type_error of string

type env
val default_env : env

val is_type_num : Type.t -> bool
val mk_equal : Expr.t -> Expr.t -> Expr.t
val mk_int : string -> Expr.t
val mk_rat : string -> Expr.t
val mk_real : string -> Expr.t

val type_tff_expr : env -> Expr.t -> Expr.t * env

val typecheck : Phrase.phrase list -> Phrase.phrase list
