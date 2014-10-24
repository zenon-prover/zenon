type env = {hypotheses : Expr.expr list;
	    distincts : (Expr.expr * int) list;}

val lltolj : env -> Llproof.prooftree -> Expr.expr -> bool 
  -> Lkproof.lkproof * Expr.expr;;
