(*  Copyright 2003 INRIA  *)
Version.add "$Id$";;



open Expr;;
open Print;;
open Node;;
open Mlproof;;


let printer e = expr_soft (Chan stdout) e;;

let rec find_first_sym t = 
  match t with 
 (*   | Evar (sym, _) -> sym *)
    | Eapp (Evar(sym, _), _, _) -> sym
    | Enot (t1, _) -> find_first_sym t1
    | _ -> ""
;;

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

let rec unif_aux l e1 e2 =
  match e1, e2 with

    | Evar (_, _), _ ->
      if  not(mem_assoc_expr e1 l) then (e1, e2)::l
      else if (assoc_expr e1 l) = e2 then l
      else raise Unif_failed

    | Eapp (Evar(f1, _), args1, _), Eapp (Evar(f2, _), args2, _) when f1 = f2 
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

let unif t1 t2 = unif_aux [] t1 t2;; 

let rec find_best_match incr left_rule fm = 
  match left_rule, fm with 
  | Evar _ , Evar _ 
    -> let new_incr = incr + 1 in 
       new_incr
  | Eapp (Evar(sym1, _), args1, _), Eapp (Evar(sym2, _), args2, _) 
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

let restore_equal fm = 
  match fm with 
(*  | Eapp ("B_equal_set", [a1; a2], _)
       when (Expr.equal a1 a2)
    -> eapp ("=", [a1; a2])
  | Enot (Eapp ("B_equal_set", [a1; a2], _), _)
       when (Expr.equal a1 a2)
    -> enot (eapp ("=", [a1; a2]))*)
  | Eapp (Evar("B_equal_set", _), [a1; a2], _)
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
	 -> eapp (evar("="), [a1; a2])
       | _, _ -> fm
     end
  | Enot (Eapp (Evar("B_equal_set", _), [a1; a2], _), _)
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
	 -> enot (eapp (evar("="), [a1; a2]))
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

      | _ -> t
    end
;;

let is_literal fm = 
  match fm with 
  | Eapp(Evar(sym, _), _, _) -> true
  | Enot(Eapp(Evar(sym, _), _, _), _) -> true
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
