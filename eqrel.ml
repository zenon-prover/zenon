(*  Copyright 2004 INRIA  *)
Version.add "$Id: eqrel.ml,v 1.3 2004-06-04 09:29:15 doligez Exp $";;

open Expr;;

exception Wrong_shape;;

let skeleton = ref None;;
let leaves = ref [];;

let rec check_pattern env pat e =
  match pat, e with
  | Eapp (sp, _, _), Eapp (se, [Evar (x, _); Evar (y, _)], _)
  | Eapp (sp, _, _), Enot (Eapp (se, [Evar (x, _); Evar (y, _)], _), _)
    when sp = se ->
      if List.mem x env && List.mem y env then ()
      else raise Wrong_shape;
  | _, _ -> raise Wrong_shape;
;;

let make_skeleton env e =
  match e with
  | Enot ((Eapp _) as e1, _) -> skeleton := Some e1;
  | Eapp _ -> skeleton := Some e;
  | _ -> raise Wrong_shape;
;;

let do_leaf env e =
  match !skeleton with
  | Some pat ->
      check_pattern env pat e;
      leaves := e :: !leaves;
  | None ->
      make_skeleton env e;
      leaves := e :: !leaves;
;;

let rec do_disj env e =
  match e with
  | Eor (e1, e2, _) -> do_disj env e1; do_disj env e2;
  | Eimply (e1, e2, _) -> do_disj env (enot e1); do_disj env e2;
  | Enot (Eand (e1, e2, _), _) -> do_disj env (enot e1); do_disj env (enot e2);
  | Enot (Enot (e1, _), _) -> do_disj env e1;
  | Etrue | Efalse -> ()
  | _ -> do_leaf env e;
;;

let get_leaves env e =
  skeleton := None;
  leaves := [];
  begin try do_disj env e; with Wrong_shape -> () end;
  !leaves
;;

let subexprs = ref [];;

let rec do_conj env e =
  match e with
  | Eand (e1, e2, _) -> do_conj env e1; do_conj env e2;
  | Eall (v, t, e1, _) -> do_conj (v::env) e1;
  | Enot (Eor (e1, e2, _), _) -> do_conj env (enot e1); do_conj env (enot e2);
  | Enot (Eimply (e1, e2, _), _) -> do_conj env e1; do_conj env (enot e2);
  | Enot (Eex (v, t, e1, _), _) -> do_conj (v::env) (enot e1);
  | Enot (Enot (e1, _), _) -> do_conj env e1;
  | Eequiv (e1, e2, _) ->
      do_conj env (eimply (e1, e2));
      do_conj env (eimply (e2, e1));
  | _ -> subexprs := (get_leaves env e) :: !subexprs;
;;

let get_subexprs e =
  subexprs := [];
  do_conj [] e;
  !subexprs
;;

let get_symbol l =
  match l with
  | Enot (Eapp (s, _, _), _) :: _ -> s
  | Eapp (s, _, _) :: _ -> s
  | _ -> assert false
;;

let rec partition pos neg l =
  match l with
  | [] -> (pos, neg)
  | (Enot _ as h) :: t -> partition pos (h::neg) t
  | h :: t -> partition (h::pos) neg t
;;

let is_refl l =
  match l with
  | [ Eapp (_, [Evar (x, _); Evar (y, _)], _) ] -> x = y
  | _ -> false
;;

let is_sym l =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _) ]
    -> x1 = y2 && y1 = x2
  | _ -> false
;;

let is_trans l =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    ->    y2 = x3 && x1 = x2 && y1 = y3
       || y3 = x2 && x1 = x3 && y1 = y2
  | _ -> false
;;

let is_transsym l =
  match partition [] [] l with
  | [ Eapp (_, [Evar (x1, _); Evar (y1, _)], _) ],
    [ Enot (Eapp (_, [Evar (x2, _); Evar (y2, _)], _), _);
      Enot (Eapp (_, [Evar (x3, _); Evar (y3, _)], _), _)]
    ->    y2 = x3 && y1 = x2 && x1 = y3
       || y3 = x2 && y1 = x3 && x1 = y2
  | _ -> false
;;

type info = {
  mutable refl : bool;
  mutable sym : bool;
  mutable trans : bool;
  mutable transsym : bool;
};;

let tbl = Hashtbl.create 97;;

let get_record s =
  try Hashtbl.find tbl s
  with Not_found ->
    let result = {refl = false; sym = false; trans = false; transsym = false} in
    Hashtbl.add tbl s result;
    result
;;

let analyse_subexpr sb =
  if is_refl sb then (get_record (get_symbol sb)).refl <- true;
  if is_sym sb then (get_record (get_symbol sb)).sym <- true;
  if is_trans sb then (get_record (get_symbol sb)).trans <- true;
  if is_transsym sb then (get_record (get_symbol sb)).transsym <- true;
;;

let analyse e = List.iter analyse_subexpr (get_subexprs e);;

let refl s =
  try let r = Hashtbl.find tbl s
      in r.refl
  with Not_found -> false
;;

let sym s =
  try let r = Hashtbl.find tbl s
      in r.sym || r.refl && r.transsym
  with Not_found -> false
;;

let trans s =
  try let r = Hashtbl.find tbl s in
      r.trans || r.refl && r.transsym
  with Not_found -> false
;;

let print_rels oc =
  let f k r =
    Printf.fprintf oc " %s:%s%s%s%s" k
                   (if r.refl then "R" else "")
                   (if r.sym then "S" else "")
                   (if r.trans then "T" else "")
                   (if r.transsym then "X" else "")
  in
  Hashtbl.iter f tbl;
;;
