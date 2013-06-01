(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
(*  $Id$  *)

val init_ext : string -> unit

val is_egal : Expr.expr -> Expr.expr list -> bool
val is_plusGrand : Expr.expr -> Expr.expr -> bool
val is_extensionnality : Expr.expr -> bool
val is_antisym : Expr.expr -> Expr.expr -> bool

val print_newnodes_mg : Expr.expr list -> unit


val maj_all :
  string -> string -> Expr.expr -> Expr.expr list list -> unit

