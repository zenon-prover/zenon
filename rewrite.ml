(*  Copyright 2003 INRIA  *)
Version.add "$Id$";;



open Expr;;
open Print;;
open Node;;
open Mlproof;;


let printer e = expr_soft (Chan stdout) e;;

let rec print_list_pair_expr l = 
  match l with 
    | [] -> print_endline ")"
    | (x1, x2)::tl 
	-> print_string "(";
	  printer x1;
	  print_string ", ";
	  printer x2;
	  print_string ")";
	  print_list_pair_expr tl
;;

let rec print_list_expr l =
  match l with 
    | [] -> (print_endline "";
	     print_endline "FIN LIST EXPR";)
    | h :: t -> 
      (print_endline " >> ";
       printer h;
       print_list_expr t)
;;

let rec print_list_de_list l =
  match l with 
    | [] -> (print_endline "";
	     print_endline "FIN LIST EXPR";)
    | h :: t -> 
      (print_string " >> ";
       printer (List.hd h);
       print_list_de_list t)
;;


let rec find_first_sym t = 
  match t with 
    | Evar (sym, _) -> sym
    | Eapp (sym, _, _) -> sym
    | Enot (t1, _) -> find_first_sym t1
    | _ -> ""
;;


(* The rename function.
   Used to rename variables of expr
   \ do not use this one
   \ try next one
*)

let rec rename_aux e l = 
  match e with 
    | Evar (v, _) -> 
      (try (List.assq e l), l with 
	| Not_found ->
	  let nv = newvar () in nv, (e, nv)::l
	| _ -> e, l)

    | Eapp (f, args, _) -> 
      let (new_args, new_l) = 
	List.fold_left 
	  (fun (new_args, n_l) t -> 
	    let (new_t,n_l2) = rename_aux t n_l in
	    new_args@[new_t],n_l2) ([],l) args in 
      (eapp (f, new_args)), new_l

    | Enot (e1, _) -> 
      let (ne, nl) = rename_aux e1 l in (enot ne), nl
    | Eand (e1, e2, _) -> 
      let (ne1, nl1) = rename_aux e1 l in 
      let (ne2, nl2) = rename_aux e2 nl1 in
      (eand (ne1, ne2)), nl2
    | Eor (e1, e2, _) -> 
      let (ne1, nl1) = rename_aux e1 l in 
      let (ne2, nl2) = rename_aux e2 nl1 in 
      (eor (ne1, ne2)), nl2 
    | Eimply (e1, e2, _) -> 
      let (ne1, nl1) = rename_aux e1 l in 
      let (ne2, nl2) = rename_aux e2 nl1 in 
      (eimply (ne1, ne2)), nl2
    | Eequiv (e1, e2, _) -> 
      let (ne1, nl1) = rename_aux e1 l in 
      let (ne2, nl2) = rename_aux e2 nl1 in 
      (eequiv (ne1, ne2)), nl2 
    | _  -> e, l;;


(* The rename function.
   Used to rename variables of expr
*)

let rename e = rename_aux e [];;


(* new assoc and mem_assoc functions
   with the Expr.equal equality
   replacing =
*)

let rec assoc_expr x = function
  | [] -> raise Not_found
  | (a,b)::l -> if (Expr.equal a x) then b else assoc_expr x l
;;

let rec mem_assoc_expr x = function
  | [] -> false
  | (a, b)::l -> (Expr.equal a x) || mem_assoc_expr x l
;;

let rec mem_expr x = function
  | [] -> false
  | a :: l -> (Expr.equal a x) || mem_expr x l
;;


exception Unif_failed;;


(* The unif_aux function.
   Used to unify two expr 
   \ do not use this one.
   \ try next one ...
*)

let rec unif_aux l e1 e2 =
  match e1, e2 with

    | Evar (_, _), _ ->
      if  not(mem_assoc_expr e1 l) then (e1, e2)::l
      else if (assoc_expr e1 l) = e2 then l
      else raise Unif_failed

    | Eapp (f1, args1, _), Eapp (f2, args2, _) when f1 = f2 
         -> (try 
	      List.fold_left2 unif_aux l args1 args2
	     with 
	       | Invalid_argument _ -> raise Unif_failed)

    | Enot (x1, _), Enot (y1, _) 
      -> unif_aux l x1 y1
    | Eand (x1, x2, _), Eand (y1, y2, _) 
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eor (x1, x2, _), Eor (y1, y2, _) 
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eimply (x1, x2, _), Eimply (y1, y2, _) 
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]
    | Eequiv (x1, x2, _), Eequiv (y1, y2, _) 
      -> List.fold_left2 unif_aux l [x1;x2] [y1;y2]

    | _, _ when (Expr.equal e1 e2) -> (e1, e2)::l
    | _, _ -> raise Unif_failed
;;


(* The unif function.
   Used to unify two expr
*)
let unif t1 t2 = unif_aux [] t1 t2;; 



(* normalisation des propositions

*)

let ordering (l1, r1) (l2, r2) = 
  let fv_l1 = get_fv l1 in
  let fv_l2 = get_fv l2 in 
  if List.length fv_l1 = List.length fv_l2 then 0
  else if List.length fv_l1 > List.length fv_l2 then 1
  else -1
;;

let rec rewrite_prop (l, r) p = 
  try
    let subst = unif l p in
    Expr.substitute subst r 

  with
  | Unif_failed -> 
    (match p with 
      | Enot (p2, _) -> 
	enot (rewrite_prop (l, r) p2)
      | _ -> p)
;;
  
let rec norm_prop_aux rules fm = 
  match rules with 
    | [] -> fm 
    | (l, r) :: tl -> 
      begin 
	let new_fm = rewrite_prop (l, r) fm in 
	if (Expr.equal fm new_fm) 
	then norm_prop_aux tl fm
	else 
	  begin
	   (* Globals.compteur_rwrt_p := !Globals.compteur_rwrt_p + 1;*)
	    new_fm
	  end 
      end 
;;

let norm_prop fm = 
  let rules = Hashtbl.find_all !Expr.tbl_prop (find_first_sym fm) in 
  let rules_sort = List.sort ordering rules in 
  norm_prop_aux rules_sort fm
;;



let rec rewrite_term (l, r) p = 
  try
    let subst = unif l p in
    Expr.substitute subst r 
  with
  | Unif_failed -> p
;;
  
let rec norm_term_aux rules t = 
  match rules with 
    | [] -> t 
    | (l, r) :: tl -> 
      norm_term_aux tl (rewrite_term (l, r) t)
;;

let rec norm_term t =
  let rules = Hashtbl.find_all !Expr.tbl_term (find_first_sym t) in 
  let rules_sort = List.sort ordering rules in 
  let new_t = norm_term_aux rules_sort t in
  if not (Expr.equal t new_t) 
  then norm_term new_t
  else 
    begin
      match t with 
      | Eapp (f, args, _) -> 
	eapp (f, (List.map norm_term args))
      | Enot (t1, _) -> 
	enot (norm_term t1)
      | Eand (t1, t2, _) -> 
	eand (norm_term t1, norm_term t2)
      | Eor (t1, t2, _) -> 
	eor (norm_term t1, norm_term t2)
      | Eimply (t1, t2, _) -> 
	eimply (norm_term t1, norm_term t2)
      | Eequiv (t1, t2, _) -> 
	eequiv (norm_term t1, norm_term t2)

  (*    | Eall (x, typex, t1, _) -> 
	eall (x, typex, norm_term t1)
      | Eex (x, typex, t1, _) -> 
	eex (x, typex, norm_term t1)
      | Etau (x, typex, t1, _) -> 
	etau (x, typex, norm_term t1)
      | Elam (x, typex, t1, _) -> 
	elam (x, typex, norm_term t1)
   *)
      | _ -> t
    end
;;

let is_litteral fm = 
  match fm with 
  | Eapp(sym, _, _) -> true
  | Enot(Eapp(sym, _, _), _) -> true
  | _ -> false
;;


let rec normalize_fm fm = 
if is_litteral fm then
  begin 
    let fm_t = norm_term fm in 
    let fm_p = norm_prop fm_t in 
    if (Expr.equal fm_p fm)
    then fm
    else normalize_fm fm_p
  end
else
  fm
;;

let rec normalize_list_aux accu list = 
  match list with 
  | [] -> List.rev accu
  | h :: t -> 
    let new_accu = (normalize_fm h) :: accu in 
    normalize_list_aux new_accu t
;;

let normalize_list list = 
  normalize_list_aux [] list
;;