val trexpr : Expr.expr -> Dkterm.term

val trproof : Lltolj.lkproof * Expr.expr * (Expr.expr * Dkterm.term) list -> Dkterm.term
