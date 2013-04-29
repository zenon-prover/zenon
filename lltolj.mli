type sequent;;
type lkrule =
| SCaxiom of Expr.expr
| SCfalse
| SCtrue
| SCeqref of Expr.expr
| SCeqsym of Expr.expr * Expr.expr
| SCeqprop of Expr.expr * Expr.expr * lkproof list
| SCeqfunc of Expr.expr * Expr.expr * lkproof list
| SCcut of Expr.expr * lkproof * lkproof
| SCland of Expr.expr * Expr.expr * lkproof
| SClor of Expr.expr * Expr.expr * lkproof * lkproof
| SClimply of Expr.expr * Expr.expr * lkproof * lkproof
| SClnot of Expr.expr * lkproof
| SClall of Expr.expr * Expr.expr * lkproof
| SClex of Expr.expr * Expr.expr * lkproof
| SClcongruence of Expr.expr * Expr.expr * Expr.expr * lkproof
| SCrand of Expr.expr * Expr.expr * lkproof * lkproof
| SCrorl of Expr.expr * Expr.expr * lkproof
| SCrorr of Expr.expr * Expr.expr * lkproof
| SCrimply of Expr.expr * Expr.expr * lkproof
| SCrnot of Expr.expr * lkproof
| SCrall of Expr.expr * Expr.expr * lkproof
| SCrex of Expr.expr * Expr.expr * lkproof
| SCrcontr of Expr.expr * lkproof

and lkproof =
  Expr.expr list * Expr.expr list * lkrule
;;

val scaxiom : Expr.expr -> lkproof;;
val scfalse : lkproof;;
val sctrue : lkproof;;
val sceqref : Expr.expr -> lkproof;;
val sceqsym : Expr.expr * Expr.expr -> lkproof;;
val sceqprop : Expr.expr * Expr.expr * lkproof list -> lkproof;;
val sceqfunc : Expr.expr * Expr.expr * lkproof list -> lkproof;;
val sccut : Expr.expr * lkproof * lkproof -> lkproof;;
val scland : Expr.expr * Expr.expr * lkproof -> lkproof;;
val sclor : 
  Expr.expr * Expr.expr * lkproof * lkproof -> lkproof;;
val sclimply :
  Expr.expr * Expr.expr * lkproof * lkproof -> lkproof;;
val sclnot : Expr.expr * lkproof -> lkproof;;
val sclall : Expr.expr * Expr.expr * lkproof -> lkproof;;
val sclex : Expr.expr * Expr.expr * lkproof -> lkproof;;
val sclcongruence : 
  Expr.expr * Expr.expr * Expr.expr * lkproof -> lkproof;;
val scrand : 
  Expr.expr * Expr.expr * lkproof * lkproof -> lkproof;;
val scrorl : Expr.expr * Expr.expr * lkproof -> lkproof;;
val scrorr : Expr.expr * Expr.expr * lkproof -> lkproof;;
val scrimply : Expr.expr * Expr.expr * lkproof -> lkproof;;
val scrnot  : Expr.expr * lkproof -> lkproof;;
val scrall : Expr.expr * Expr.expr * lkproof -> lkproof;;
val screx : Expr.expr * Expr.expr * lkproof -> lkproof;;
val scrcontr : Expr.expr * lkproof -> lkproof;;

val lemma_env : (string, Llproof.prooftree) Hashtbl.t;;
val hypothesis_env : Expr.expr list ref;;
val definition_env : (string, Expr.expr list * Expr.expr) Hashtbl.t;;
val lltolj : Llproof.prooftree -> Expr.expr -> (Expr.expr * lkproof);;
exception Found of Expr.expr;;
