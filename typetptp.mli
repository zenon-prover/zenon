
exception Type_error of string

val bnot : Expr.t -> Expr.t
val print_expr : Format.formatter -> Expr.expr -> unit
val typecheck : Phrase.phrase list -> Phrase.phrase list
