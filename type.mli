
exception Type_error of string

val print_expr : Format.formatter -> Expr.expr -> unit
val typecheck : Phrase.phrase list -> Phrase.phrase list
