(*  Copyright 2012-2013 Cnam and Siemens IC-MOL  *)
Version.add "$Id$";;

let rules : ((Expr.expr,string*(Expr.expr list list)) Hashtbl.t)=
Hashtbl.create 100;;

module HE = Hashtbl.Make (Expr);;

let tblsize = 997;;  (* reduce to 17 for debugging *)
let allforms = (HE.create tblsize : int HE.t);;

let member_he e = HE.mem allforms e;;

let add_he e g =
  HE.add allforms e g;;
let remove_he e =
  HE.remove allforms e
;;
let clear_he ()=
  HE.clear allforms
;;

let get_all_he () = HE.fold (fun e g l -> (e, g) :: l) allforms [];;

let formules : ((Expr.expr,string*(Expr.expr list list)) Hashtbl.t)=
Hashtbl.create 100;;

let newnodes_mg = ref [];;
