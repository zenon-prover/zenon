type sequent;;
type lkrule =
| SCAxiom of Expr.expr
| SCFalse
| SCTrue
| SCEqref of Expr.expr
| SCEqsym of Expr.expr * Expr.expr
| SCEqprop of Expr.expr * Expr.expr * lkrule list
| SCEqfunc of Expr.expr * Expr.expr * lkrule list
| SCCut of Expr.expr * lkrule * lkrule
| SCLand of Expr.expr * Expr.expr * lkrule
| SCLor of Expr.expr * Expr.expr * lkrule * lkrule
| SCLimply of Expr.expr * Expr.expr * lkrule * lkrule
| SCLnot of Expr.expr * lkrule
| SCLall of Expr.expr * Expr.expr * lkrule
| SCLex of Expr.expr * Expr.expr * lkrule
| SCLcongruence of Expr.expr * Expr.expr * Expr.expr * lkrule
| SCRand of Expr.expr * Expr.expr * lkrule * lkrule
| SCRorl of Expr.expr * Expr.expr * lkrule
| SCRorr of Expr.expr * Expr.expr * lkrule
| SCRimply of Expr.expr * Expr.expr * lkrule
| SCRnot of Expr.expr * lkrule
| SCRall of Expr.expr * Expr.expr * lkrule
| SCRex of Expr.expr * Expr.expr * lkrule
| SCRweak of Expr.expr * lkrule
| SCRcontr of Expr.expr * lkrule
;;

val lemma_env : (string, Llproof.prooftree) Hashtbl.t;;
val hypothesis_env : Expr.expr list ref;;
val definition_env : (string, Expr.expr list * Expr.expr) Hashtbl.t;;
val lltolj : Llproof.prooftree -> Expr.expr -> (Expr.expr * lkrule);;
exception Found of Expr.expr;;
