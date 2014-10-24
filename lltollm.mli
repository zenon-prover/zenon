val lltollm_expr : (string, Expr.expr list * Expr.t) Hashtbl.t -> Expr.expr -> Expr.expr
val lltollm_proof : (string, Expr.expr list * Expr.expr) Hashtbl.t -> (string, Llproof.prooftree) Hashtbl.t -> Llproof.prooftree -> Llproof.prooftree;;
val lltollm_env : (string, Expr.expr list * Expr.expr) Hashtbl.t -> Llmtolk.env -> Llmtolk.env
