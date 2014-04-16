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

let rec print_rules l = 
  match l with 
  | [] -> print_endline " -- -- end rules -- -- "
  | (l, r) :: tl -> 
     printer l; 
     print_string "  -->  "; 
     printer r; 
     print_endline "";
     print_rules tl
;;


let rec find_first_sym t = 
  match t with 
 (*   | Evar (sym, _) -> sym *)
    | Eapp (sym, _, _) -> sym
    | Enot (t1, _) -> find_first_sym t1
    | _ -> ""
;;

let find_sym_args t = 
  match t with
  | Evar _ -> "useless_variable"
  | Eapp ( sym, _, _) -> sym
  | _ -> assert false
;;

let rec find_syms t =
  match t with
  | Eapp (sym, args, _) -> 
     (sym, List.length args, List.map find_sym_args args)
  | Enot (f, _) -> find_syms f
  | _ -> assert false
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

let rec find_best_match incr left_rule fm = 
  match left_rule, fm with 
  | Evar _ , Evar _ 
    -> let new_incr = incr + 1 in 
       new_incr
  | Eapp (sym1, args1, _), Eapp (sym2, args2, _) 
       when sym1 = sym2 && List.length args1 = List.length args2
    -> let new_incr = incr + 3 in 
       List.fold_left2 find_best_match new_incr args1 args2
  | Eapp _, _ 
    -> let new_incr = incr - 1 in 
       new_incr
  | _, _ -> incr
;; 

let ordering_two fm (l1, r1) (l2, r2) =
  match fm with 
  | Enot (r_fm, _) 
    -> 
     begin
       if find_best_match 0 l1 r_fm = find_best_match 0 l2 r_fm 
       then 0
       else if find_best_match 0 l1 r_fm < find_best_match 0 l2 r_fm 
       then 1
       else -1
     end
  | _  -> 
     begin
       if find_best_match 0 l1 fm = find_best_match 0 l2 fm 
       then 0
       else if find_best_match 0 l1 fm < find_best_match 0 l2 fm 
       then 1
       else -1
     end
;; 

 let ordering (l1, r1) (l2, r2) = 
  let fv_l1 = get_fv l1 in
  let fv_l2 = get_fv l2 in 
  if List.length fv_l1 = List.length fv_l2 then 0
  else if List.length fv_l1 > List.length fv_l2 then 1
  else -1
;; 

(* let equal_is_equal rules fm = 
  match fm with 
  | Eapp ("=", [a1; a2], _)
  | Enot ( Eapp ("=", [a1; a2], _), _)
    -> 
     begin
       match a1, a2 with 
       | _, _ when Expr.equal a1 a2 
	 -> [] (*[(eapp ("=", [evar("x"); evar("y")]),
	      eapp ("=", [evar("x"); evar("y")]))] *)
       
       | Eapp _, _
       | _, Eapp _ -> rules
       | _, _ -> [] (* [(eapp ("=", [evar("x"); evar("y")]),
		   eapp ("=", [evar("x"); evar("y")]))] *)
     end
  | _ -> rules
;; *)

(*let equal_is_equal rules fm = 
  match fm with 
  | Eapp ("=", [a1; a2], _)
       when Expr.equal a1 a2
    -> []
  | Enot (Eapp ("=", [a1; a2], _), _)
       when Expr.equal a1 a2
    -> []
  | Eapp ("=", [a1; a2], _)
    ->
     begin
       match a1, a2 with 
       | Emeta _, _
       | _, Emeta _
	 -> []
       | Eapp _, _
       | _, Eapp _
	 -> rules
       | _, _ -> []
     end
  | Enot (Eapp ("=", [a1; a2], _), _)
    -> 
     begin
       match a1, a2 with
       | Emeta _, _
       | _, Emeta _
	 -> []
       | Eapp _, _
       | _, Eapp _
	 -> rules
       | _, _ -> []
     end
  | _ -> rules
;;*)

let restore_equal fm = 
  match fm with 
(*  | Eapp ("B_equal_set", [a1; a2], _)
       when (Expr.equal a1 a2)
    -> eapp ("=", [a1; a2])
  | Enot (Eapp ("B_equal_set", [a1; a2], _), _)
       when (Expr.equal a1 a2)
    -> enot (eapp ("=", [a1; a2]))*)
  | Eapp ("B_equal_set", [a1; a2], _)
    ->
     begin
       match a1, a2 with 
       | Evar _, Evar _
       | Evar _, Emeta _
       | Emeta _, Evar _
       | Emeta _, Emeta _
       | Etau _, Etau _
       | Evar _, Etau _
       | Etau _, Evar _
       | Emeta _, Etau _
       | Etau _, Emeta _
	 -> eapp ("=", [a1; a2])
       | _, _ -> fm
     end
  | Enot (Eapp ("B_equal_set", [a1; a2], _), _)
    ->
     begin
       match a1, a2 with 
       | Evar _, Evar _
       | Evar _, Emeta _
       | Emeta _, Evar _
       | Emeta _, Emeta _
       | Etau _, Etau _
       | Evar _, Etau _
       | Etau _, Evar _
       | Emeta _, Etau _
       | Etau _, Emeta _
	 -> enot (eapp ("=", [a1; a2]))
       | _, _ -> fm
     end
  | _ -> fm
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
	    if !Globals.debug_flag || !Globals.debug_rwrt
	    then 
	      begin
		print_endline "";
		print_endline " -- Rewriting Prop -- ";
		print_string "Fm : ";
		printer fm;
		print_string " --> ";
		printer new_fm;
		print_endline "";
		print_endline "";
	      end;
	    new_fm
	  end 
      end 
;;

let norm_prop fm = 
  
  let rules = Hashtbl.find_all !Expr.tbl_prop (find_first_sym fm) in

  let rules_sort = List.sort (ordering_two fm) rules in

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
(*  let rules_sort = List.sort ordering rules in *)
  let rules_sort = List.sort (ordering_two t) rules in
  let new_t = norm_term_aux rules_sort t in
  if not (Expr.equal t new_t) 
  then 
    begin 
      if !Globals.debug_flag || !Globals.debug_rwrt
      then 
	begin
	  print_endline "";
	  print_endline " -- Rewriting Term -- ";
	  print_string "t : ";
	  printer t;
	  print_string " --> ";
	  printer new_t;
	  print_endline "";
	  print_endline "";
	end;
      norm_term new_t
    end
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

   (*   | Eall (x, typex, t1, _) -> 
	eall (x, typex, norm_term t1)
      | Eex (x, typex, t1, _) -> 
	eex (x, typex, norm_term t1)
      | Etau (x, typex, t1, _) -> 
	etau (x, typex, norm_term t1)
      | Elam (x, typex, t1, _) -> 
	elam (x, typex, norm_term t1) *)

      | _ -> t
    end
;;

let is_literal fm = 
  match fm with 
  | Eapp(sym, _, _) -> true
  | Enot(Eapp(sym, _, _), _) -> true
  | _ -> false
;;


let rec normalize_fm fm = 
(*  let fm = restore_equal fm in*)
  if is_literal fm then
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
