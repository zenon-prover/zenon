
(* Module for arithemtic functions *)


exception NotaFormula
exception EndReached

(* Type manipulation *)
val get_type : Expr.expr -> Expr.typ
val is_int : Expr.expr -> bool
val is_rat : Expr.expr -> bool
val ctype : string -> string -> string
val etype : Expr.expr -> Expr.expr -> string

val is_z : Q.t -> bool
val is_q : Q.t -> bool
val floor : Q.t -> Q.t
val ceil : Q.t -> Q.t

(* Expression manipulation *)
val comp_neg : string -> string
val mk_app : Expr.typ -> string -> Expr.expr list -> Expr.expr

(* Expression construction *)
val const : string -> Expr.expr
val sum : Expr.expr -> Expr.expr -> Expr.expr
val diff : Expr.expr -> Expr.expr -> Expr.expr
val uminus : Expr.expr -> Expr.expr
val mul : Expr.expr -> Expr.expr -> Expr.expr
val minus_one : Expr.expr -> Expr.expr
val plus_one : Expr.expr -> Expr.expr

val eeq : Expr.expr -> Expr.expr -> Expr.expr
val less : Expr.expr -> Expr.expr -> Expr.expr
val lesseq : Expr.expr -> Expr.expr -> Expr.expr
val greater : Expr.expr -> Expr.expr -> Expr.expr
val greatereq : Expr.expr -> Expr.expr -> Expr.expr

(* Formula manipulation *)
val find_coef : Expr.t -> ('a * Expr.t) list -> 'a

val fadd : (Q.t * Expr.t) list -> (Q.t * Expr.t) list -> (Q.t * Expr.t) list
val fdiff : (Q.t * Expr.t) list -> (Q.t * Expr.t) list -> (Q.t * Expr.t) list
val fmul : Q.t -> (Q.t * 'a) list -> (Q.t * 'a) list

val sanitize : (Q.t * 'a) list -> (Q.t * 'a) list
val normalize :
  (Q.t * Expr.t) list -> (Q.t * Expr.t) list -> Q.t * (Q.t * Expr.t) list

(* Conversion functions *)
val of_cexpr : Expr.expr -> Q.t
val of_nexpr : Expr.t -> (Q.t * Expr.t) list
val of_bexpr : Expr.expr -> (Q.t * Expr.t) list * string * Q.t

val to_nexpr : (Q.t * Expr.expr) list -> Expr.expr
val to_bexpr : (Q.t * Expr.expr) list * string * Q.t -> Expr.expr

val expr_norm : Expr.expr -> Expr.expr


(* Choice trees *)
type 'a clist
val cl_from_list : 'a list -> 'a clist
val cl_current : 'a clist -> 'a
val cl_next : 'a clist -> unit
val cl_reset : 'a clist -> unit

type 'a ctree = {
    node : 'a clist;
    children : 'a ctree array;
}

val reset : 'a ctree -> unit
val next : 'a ctree -> unit
val current : 'a ctree -> 'a list
val ct_all : 'a ctree -> 'a list list

(* Simplex solver helper *)
val try_solve : Expr.t list -> (Expr.t * Q.t) list option


