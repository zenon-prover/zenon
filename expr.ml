(*  Copyright 2002 INRIA  *)
Version.add "$Id: expr.ml,v 1.12 2004-10-18 16:53:28 doligez Exp $";;

open Misc;;

let _equal = ( = );;
let ( = ) = ();;
let string_equal x y = String.compare x y == 0;;

type expr =
  | Evar of string * private_info
  | Emeta of expr * private_info
  | Eapp of string * expr list * private_info

  | Enot of expr * private_info
  | Eand of expr * expr * private_info
  | Eor of expr * expr * private_info
  | Eimply of expr * expr * private_info
  | Eequiv of expr * expr * private_info
  | Etrue
  | Efalse

  | Eall of expr * string * expr * private_info
  | Eex of expr * string * expr * private_info
  | Etau of expr * string * expr * private_info

and private_info = {
  hash : int;
  skel_hash : int;
  free_vars : string list;
  size : int;
  metas : expr list;
};;

type definition =
  | DefReal of string * expr list * expr
  | DefPseudo of (expr * int) * string * expr list * expr
;;


(************************)
(* small sets of formulas (represented as lists) *)

let rec diff l1 l2 =
  match l1 with
  | [] -> []
  | e::t -> if List.exists ((==) e) l2
            then diff t l2
            else e :: (diff t l2)
;;

let union l1 l2 = (diff l1 l2) @@ l2;;

let rec disjoint l1 l2 =
  match l1 with
  | [] -> true
  | h::t -> if List.exists ((==) h) l2
            then false
            else disjoint t l2
;;

(*******************)

let k_true = 123000
and k_false = 456
and k_meta = 27182818
and k_app = 14142135
and k_not = 997
and k_and = 11003
and k_or = 100007
and k_imply = 43011
and k_equiv = 121013
and k_all = 31415926
and k_ex = 223017
and k_tau = 323019
;;

let size_meta = 15;;
let size_tau_inverse = 1000;;

let mkpriv skel fv sz metas = {
  hash = Hashtbl.hash (skel, fv);
  skel_hash = skel;
  free_vars = fv;
  size = sz;
  metas = metas;
};;

let priv_true = mkpriv k_true [] 1 [];;
let priv_false = mkpriv k_false [] 1 [];;

let get_priv = function
  | Evar (_, h) -> h
  | Emeta (_, h) -> h
  | Eapp (_, _, h) -> h

  | Enot (_, h) -> h
  | Eand (_, _, h) -> h
  | Eor (_, _, h) -> h
  | Eimply (_, _, h) -> h
  | Eequiv (_, _, h) -> h
  | Etrue -> priv_true
  | Efalse -> priv_false

  | Eall (_, _, _, h) -> h
  | Eex (_, _, _, h) -> h
  | Etau (_, _, _, h) -> h
;;

let get_hash e = (get_priv e).hash;;
let get_skel e = (get_priv e).skel_hash;;
let get_fv e = (get_priv e).free_vars;;
let get_size e = (get_priv e).size;;
let get_metas e = (get_priv e).metas;;

let rec str_union l1 l2 =
  match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | h::t, _ when List.exists (string_equal h) l2 -> str_union t l2
  | h::t, _ -> str_union t (h :: l2)
;;

let rec remove x l =
  match x, l with
  | _, [] -> []
  | Evar (v, _), h::t when string_equal v h -> t
  | _, h::t -> h :: (remove x t)
;;

let combine x y = (x lsl 1) + (x lsr 30) + y;;

let priv_var s = mkpriv 0 [s] 1 [];;
let priv_meta e =
  mkpriv (combine k_meta (get_skel e)) (get_fv e) size_meta [e]
;;
let priv_app s args =
  let comb_skel sk e = combine sk (get_skel e) in
  let skel = combine k_app (List.fold_left comb_skel (Hashtbl.hash s) args) in
  let sz = List.fold_left (fun a e -> a + get_size e) 1 args in
  let metas = List.fold_left (fun a e -> union (get_metas e) a) [] args in
  mkpriv skel (List.fold_left str_union [] (List.map get_fv args)) sz metas
;;
let priv_not e =
  mkpriv (combine k_not (get_skel e)) (get_fv e) (get_size e + 1) (get_metas e)
;;
let priv_and e1 e2 =
  mkpriv (combine k_and (combine (get_skel e1) (get_skel e2)))
         (str_union (get_fv e1) (get_fv e2))
         (get_size e1 + get_size e2 + 1)
         (union (get_metas e1) (get_metas e2))
;;
let priv_or e1 e2 =
  mkpriv (combine k_or (combine (get_skel e1) (get_skel e2)))
         (str_union (get_fv e1) (get_fv e2))
         (get_size e1 + get_size e2 + 1)
         (union (get_metas e1) (get_metas e2))
;;
let priv_imply e1 e2 =
  mkpriv (combine k_imply (combine (get_skel e1) (get_skel e2)))
         (str_union (get_fv e1) (get_fv e2))
         (get_size e1 + get_size e2 + 1)
         (union (get_metas e1) (get_metas e2))
;;
let priv_equiv e1 e2 =
  mkpriv (combine k_equiv (combine (get_skel e1) (get_skel e2)))
         (str_union (get_fv e1) (get_fv e2))
         (get_size e1 + get_size e2 + 1)
         (union (get_metas e1) (get_metas e2))
;;
let priv_all v t e =
  mkpriv (combine k_all (get_skel e)) (remove v (get_fv e))
         (1 + get_size e) (get_metas e)
;;
let priv_ex v t e =
  mkpriv (combine k_ex (get_skel e)) (remove v (get_fv e))
         (1 + get_size e) (get_metas e)
;;
let priv_tau v t e =
  mkpriv (combine k_tau (get_skel e)) (remove v (get_fv e))
         (1 + get_size e / size_tau_inverse) (get_metas e)
;;


module HashedExpr = struct
  type t = expr;;

  let hash = get_hash;;

  type binding = Bound of int | Free of expr;;

  let get_binding env v =
    let rec index i v env =
      match env with
      | x :: t when x == v -> Bound i
      | _ :: t -> index (i+1) v t
      | [] -> Free v
    in
    index 0 v env
  ;;

  let same_binding env1 v1 env2 v2 =
    match (get_binding env1 v1), (get_binding env2 v2) with
    | Bound i1, Bound i2 -> i1 == i2
    | Free w1, Free w2 -> w1 == w2
    | _, _ -> false
  ;;

  let rec equal_in_env env1 env2 e1 e2 =
    match e1, e2 with
    (* FIXME TODO court-circuit si env1 et/ou env2 est irrelevant *)
    | Evar _, Evar _ -> same_binding env1 e1 env2 e2
    | Emeta (f1, _), Emeta (f2, _) -> equal_in_env env1 env2 f1 f2
    | Eapp (sym1, args1, _), Eapp (sym2, args2, _) ->
        string_equal sym1 sym2
        && List.for_all2 (equal_in_env env1 env2) args1 args2
    | Enot (f1, _), Enot (f2, _) -> equal_in_env env1 env2 f1 f2
    | Eand (f1, g1, _), Eand (f2, g2, _)
    | Eor (f1, g1, _), Eor (f2, g2, _)
    | Eimply (f1, g1, _), Eimply (f2, g2, _)
    | Eequiv (f1, g1, _), Eequiv (f2, g2, _)
      -> equal_in_env env1 env2 f1 f2 && equal_in_env env1 env2 g1 g2
    | Efalse, Efalse
    | Etrue, Etrue
      -> true
    | Eall (v1, t1, f1, _), Eall (v2, t2, f2, _)
    | Eex (v1, t1, f1, _), Eex (v2, t2, f2, _)
    | Etau (v1, t1, f1, _), Etau (v2, t2, f2, _)
      -> equal_in_env (v1::env1) (v2::env2) f1 f2
    | _, _ -> false
  ;;

  let equal e1 e2 =
    match e1, e2 with
    | Evar (v1, _), Evar (v2, _) -> string_equal v1 v2
    | Emeta (f1, _), Emeta (f2, _) -> f1 == f2
    | Eapp (sym1, args1, _), Eapp (sym2, args2, _) ->
        string_equal sym1 sym2 && List.for_all2 (==) args1 args2
    | Enot (f1, _), Enot (f2, _) -> f1 == f2
    | Eand (f1, g1, _), Eand (f2, g2, _)
    | Eor (f1, g1, _), Eor (f2, g2, _)
    | Eimply (f1, g1, _), Eimply (f2, g2, _)
    | Eequiv (f1, g1, _), Eequiv (f2, g2, _)
      -> f1 == f2 && g1 == g2
    | Eall (v1, t1, f1, _), Eall (v2, t2, f2, _)
    | Eex (v1, t1, f1, _), Eex (v2, t2, f2, _)
    | Etau (v1, t1, f1, _), Etau (v2, t2, f2, _)
      -> string_equal t1 t2
         && (v1 == v2 && f1 == f2
            || equal_in_env [v1] [v2] f1 f2)
    | _, _ -> false
  ;;
end;;

(* Weak table version *)

module HE = Weak.Make (HashedExpr);;
let tbl = HE.create 999997;;

let he_merge k =
  try HE.find tbl k
  with Not_found ->
    incr Globals.num_expr;
    HE.add tbl k;
    k
;;

(* Normal table version (faster but uses more memory) *)
(*
  module HE = Hashtbl.Make (HashedExpr);;
  let tbl = HE.create 999997;;

  let he_merge k =
    try HE.find tbl k
    with Not_found ->
      incr Globals.num_expr;
      HE.add tbl k k;
      k
  ;;
*)

let evar (s) = he_merge (Evar (s, priv_var s));;
let emeta (e) = he_merge (Emeta (e, priv_meta e));;
let eapp (s, args) = he_merge (Eapp (s, args, priv_app s args));;
let enot (e) = he_merge (Enot (e, priv_not e));;
let eand (e1, e2) = he_merge (Eand (e1, e2, priv_and e1 e2));;
let eor (e1, e2) = he_merge (Eor (e1, e2, priv_or e1 e2));;
let eimply (e1, e2) = he_merge (Eimply (e1, e2, priv_imply e1 e2));;
let etrue = Etrue;;
let efalse = Efalse;;
let eequiv (e1, e2) = he_merge (Eequiv (e1, e2, priv_equiv e1 e2));;
let eall (v, t, e) = he_merge (Eall (v, t, e, priv_all v t e));;
let eex (v, t, e) = he_merge (Eex (v, t, e, priv_ex v t e));;
let etau (v, t, e) = he_merge (Etau (v, t, e, priv_tau v t e));;

type t = expr;;
let hash = get_hash;;
let equal = (==);;
let cmp x y =
  match compare (hash x) (hash y) with
  | 0 -> if equal x y then 0 else compare x y
  | x when x < 0 -> -1
  | _ -> 1
;;

(************************)

exception Mismatch;;

let rec xpreunify accu e1 e2 =
  match e1, e2 with
  | _, _ when e1 == e2 -> accu
  | Eapp (s1, a1, _), Eapp (s2, a2, _) when string_equal s1 s2 ->
      List.fold_left2 xpreunify accu a1 a2
  | Emeta _, _ -> (e1, e2) :: accu
  | _, Emeta _ -> (e2, e1) :: accu
  | _, _ -> raise Mismatch
;;

let preunify e1 e2 =
  try xpreunify [] e1 e2
  with Mismatch -> []
;;

let preunifiable e1 e2 =
  try ignore (xpreunify [] e1 e2);
      true
  with Mismatch -> false
;;

let occurs_as_meta e f = List.exists ((==) e) (get_metas f);;
let size = get_size;;
let has_metas e = get_metas e <> [];;
let count_metas e = List.length (get_metas e);;

let cursym = ref "_Z";;

let rec incr_sym n =
  if n >= String.length !cursym
  then cursym := !cursym ^ "a"
  else match !cursym.[n] with
  | 'z' -> !cursym.[n] <- 'a'; incr_sym (n+1)
  | c -> !cursym.[n] <- Char.chr (1 + Char.code c)
;;

let newvar () =
  incr_sym 2;
  evar (String.copy !cursym)
;;

let rec rm_binding v map =
  match map with
  | [] -> []
  | (w, _) :: t when w == v -> t
  | h :: t -> h :: (rm_binding v t)
;;

let conflict v map =
  match v with
  | Evar (vv, _) ->
      List.exists (fun (w, e) -> List.mem vv (get_fv e)) map
  | _ -> assert false
;;

let disj vars map =
  let diff_var v e =
    match e with
    | Evar (w, _), _ -> not (string_equal v w)
    | _ -> assert false
  in
  let irrelevant v = List.for_all (diff_var v) map in
  List.for_all irrelevant vars
;;

let rec substitute map e =
  match e with
  | _ when disj (get_fv e) map -> e
  | Evar (v, _) -> (try List.assq e map with Not_found -> e)
  | Emeta (f, _) -> emeta (substitute map f)
  | Eapp (s, args, _) -> eapp (s, List.map (substitute map) args)
  | Enot (f, _) -> enot (substitute map f)
  | Eand (f, g, _) -> eand (substitute map f, substitute map g)
  | Eor (f, g, _) -> eor (substitute map f, substitute map g)
  | Eimply (f, g, _) -> eimply (substitute map f, substitute map g)
  | Eequiv (f, g, _) -> eequiv (substitute map f, substitute map g)
  | Etrue | Efalse -> e
  | Eall (v, t, f, _) ->
      let map1 = rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        eall (nv, t, substitute ((v, nv) :: map1) f)
      else
        eall (v, t, substitute map1 f)
  | Eex (v, t, f, _) ->
      let map1 = rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        eex (nv, t, substitute ((v, nv) :: map1) f)
      else
        eex (v, t, substitute map1 f)
  | Etau (v, t, f, _) ->
      let map1 = rm_binding v map in
      if conflict v map1 then
        let nv = newvar () in
        etau (nv, t, substitute ((v, nv) :: map1) f)
      else
        etau (v, t, substitute map1 f)
;;

let rec fv_rec sort bvl fvl = function
  | Evar (x, _) ->
    if List.mem_assoc x fvl || List.mem x bvl then fvl
    else (x, (sort, 0)) :: fvl
  | Eapp (f, args, _) ->
    let nfvl = if List.mem_assoc f fvl || List.mem f bvl then fvl
               else (f, (sort, List.length args)) :: fvl in
    List.fold_left (fv_rec false bvl) nfvl args
  | Enot (e, _) -> fv_rec true bvl fvl e
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
  | Eequiv (e1, e2, _) ->
    let fvl1 = fv_rec true bvl fvl e1 in fv_rec true bvl fvl1 e2
  | Eall (Evar (x, _), _, e, _)
  | Eex (Evar (x, _), _, e, _)
    -> fv_rec true (x :: bvl) fvl e
  | _ -> fvl

let free_var = fv_rec true [] []

let rec type_list_rec l = function
  | Eall (_, t, e, _) | Eex(_, t, e, _) | Etau (_, t, e, _) -> 
    let t = if string_equal t "" then "Any" else t in
    if (List.mem t l) then type_list_rec l e
    else type_list_rec (t :: l) e
  | Enot (e, _) -> type_list_rec l e
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
  | Eequiv (e1, e2, _) -> let l1 = type_list_rec l e1 in type_list_rec l1 e2
  | _ -> l

let type_list = type_list_rec []

(*let rec type_list_rec l = function
  | Eall (_, t, e, _) | Eex(_, t, e, _) | Etau (_, t, e, _) -> 
    if t = "" || (List.mem t l) then type_list_rec l e
    else type_list_rec (t::l) e
  | Enot (e, _) -> type_list_rec l e
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
  | Eequiv (e1, e2, _) -> let l1 = type_list_rec l e1 in type_list_rec l1 e2
  | _ -> l

let type_list = type_list_rec []*)
