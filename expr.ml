(*  Copyright 2002 INRIA  *)
Version.add "$Id: expr.ml,v 1.4 2004-05-25 11:41:56 doligez Exp $";;

open Misc;;

type expr =
  | Evar of string * int
  | Emeta of expr * int
  | Eapp of string * expr list * int

  | Enot of expr * int
  | Eand of expr * expr * int
  | Eor of expr * expr * int
  | Eimply of expr * expr * int
  | Eequiv of expr * expr * int
  | Etrue
  | Efalse

  | Eall of string * string * expr * int
  | Eex of string * string * expr * int
  | Etau of string * string * expr * int
;;

type definition =
  | DefReal of string * string list * expr
  | DefPseudo of (expr * int) * string * string list * expr
;;

let get_hash = function
  | Evar (s, h) -> h
  | Emeta (e, h) -> h
  | Eapp (s, args, h) -> h

  | Enot (_, h) -> h
  | Eand (_, _, h) -> h
  | Eor (_, _, h) -> h
  | Eimply (_, _, h) -> h
  | Eequiv (_, _, h) -> h
  | Etrue -> 123000
  | Efalse -> 456

  | Eall (_, _, _, h) -> h
  | Eex (_, _, _, h) -> h
  | Etau (_, _, _, h) -> h
;;

let rec index i v env =
  match env with
  | x :: t when x = v -> i
  | _ :: t -> index (i+1) v t
  | [] -> raise Not_found
;;

type binding =
  | Bound of int
  | Free of string
;;

let get_binding env v =
  try Bound (index 0 v env)
  with Not_found -> Free v
;;

let combine x y = (x lsl 1) + (x lsr 30) + y;;

let hash_var s = (Hashtbl.hash s) land max_int;;
let hash_meta e = (combine 27182818 (get_hash e)) land max_int;;
let hash_app s args =
  let hash_comb h e = combine h (get_hash e) in
  let r = combine 14142135 (List.fold_left hash_comb (Hashtbl.hash s) args) in
  r land max_int
;;
let hash_not e = (combine 997 (get_hash e)) land max_int;;
let hash_and e1 e2 =
  (combine 11003 (combine (get_hash e1) (get_hash e2))) land max_int
;;
let hash_or e1 e2 =
  (combine 100007 (combine (get_hash e1) (get_hash e2))) land max_int
;;
let hash_imply e1 e2 =
  (combine 43011 (combine (get_hash e1) (get_hash e2))) land max_int
;;
let hash_equiv e1 e2 =
  (combine 121013 (combine (get_hash e1) (get_hash e2))) land max_int
;;
let hash_true = get_hash Etrue;;
let hash_false = get_hash Efalse;;
let hash_equal e1 e2 =
  (combine 431023 (combine (get_hash e1) (get_hash e2))) land max_int
;;

let rec hash_aux env e =
  match e with
  | Evar (v, h) ->
      begin try index 0 v env
      with Not_found -> h
      end
  | Emeta (e, h) -> h
  | Eapp (sym, args, _) ->
     let hash_comb h e = combine h (hash_aux env e) in
     combine 14142135 (List.fold_left hash_comb (Hashtbl.hash sym) args)
  | Enot (e, _) -> combine 997 (hash_aux env e)
  | Eand (e1, e2, _) ->
      combine 11003 (combine (hash_aux env e1) (hash_aux env e2))
  | Eor (e1, e2, _) ->
      combine 100007 (combine (hash_aux env e1) (hash_aux env e2))
  | Eimply (e1, e2, _) ->
      combine 43011 (combine (hash_aux env e1) (hash_aux env e2))
  | Eequiv (e1, e2, _) ->
      combine 121013 (combine (hash_aux env e1) (hash_aux env e2))
  | Etrue -> hash_true
  | Efalse -> hash_false
  | Eall (v, t, e, _) -> combine 31415926 (hash_aux (v::env) e)
  | Eex (v, t, e, _) -> combine 223017 (hash_aux (v::env) e)
  | Etau (v, t, e, _) -> combine 323019 (hash_aux (v::env) e)
;;

let hash_all v t e = (combine 31415926 (hash_aux [v] e)) land max_int;;
let hash_ex v t e = (combine 223017 (hash_aux [v] e)) land max_int;;
let hash_tau v t e = (combine 323019 (hash_aux [v] e)) land max_int;;

module HashedExpr = struct
  type t = expr;;

  let hash = get_hash;;

  let rec equal_in_env env1 env2 e1 e2 =
    match e1, e2 with
    | Evar (v1, _), Evar (v2, _) -> get_binding env1 v1 = get_binding env2 v2
    | Emeta (e1, _), Emeta (e2, _) -> e1 == e2
    | Eapp (sym1, args1, _), Eapp (sym2, args2, _) ->
       sym1 = sym2 && List.for_all2 (equal_in_env env1 env2) args1 args2
    | Enot (f1, _), Enot (f2, _) -> equal_in_env env1 env2 f1 f2
    | Eand (f1, g1, _), Eand (f2, g2, _) ->
        equal_in_env env1 env2 f1 f2 && equal_in_env env1 env2 g1 g2
    | Eor (f1, g1, _), Eor (f2, g2, _) ->
        equal_in_env env1 env2 f1 f2 && equal_in_env env1 env2 g1 g2
    | Eimply (f1, g1, _), Eimply (f2, g2, _) ->
        equal_in_env env1 env2 f1 f2 && equal_in_env env1 env2 g1 g2
    | Eequiv (f1, g1, _), Eequiv (f2, g2, _) ->
        equal_in_env env1 env2 f1 f2 && equal_in_env env1 env2 g1 g2
    | Efalse, Efalse -> true
    | Eall (v1, t1, f1, _), Eall (v2, t2, f2, _) ->
        equal_in_env (v1::env1) (v2::env2) f1 f2
    | Eex (v1, t1, f1, _), Eex (v2, t2, f2, _) ->
        equal_in_env (v1::env1) (v2::env2) f1 f2
    | Etau (v1, t1, f1, _), Etau (v2, t2, f2, _) ->
        equal_in_env (v1::env1) (v2::env2) f1 f2
    | _, _ -> false
  ;;

  let equal e1 e2 =
    match e1, e2 with
    | Evar (v1, _), Evar (v2, _) -> v1 = v2
    | Emeta (f1, _), Emeta (f2, _) -> f1 == f2
    | Eapp (sym1, args1, _), Eapp (sym2, args2, _) ->
        sym1 = sym2 && List.for_all2 (==) args1 args2
    | Enot (f1, _), Enot (f2, _) -> f1 == f2
    | Eand (f1, g1, _), Eand (f2, g2, _) -> f1 == f2 && g1 == g2
    | Eor (f1, g1, _), Eor (f2, g2, _) -> f1 == f2 && g1 == g2
    | Eimply (f1, g1, _), Eimply (f2, g2, _) -> f1 == f2 && g1 == g2
    | Eequiv (f1, g1, _), Eequiv (f2, g2, _) -> f1 == f2 && g1 == g2
    | Eall (v1, t1, f1, _), Eall (v2, t2, f2, _) ->
        t1 = t2 && equal_in_env [v1] [v2] f1 f2
    | Eex (v1, t1, f1, _), Eex (v2, t2, f2, _) ->
        t1 = t2 && equal_in_env [v1] [v2] f1 f2
    | Etau (v1, t1, f1, _), Etau (v2, t2, f2, _) ->
        t1 = t2 && equal_in_env [v1] [v2] f1 f2
    | _, _ -> false
  ;;
end;;

(* Weak table version *)

module HE = Weak.Make (HashedExpr);;
let tbl = HE.create 997;;

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
  let tbl = HE.create 997;;

  let he_merge k =
    try HE.find tbl k
    with Not_found ->
      incr Globals.num_expr;
      HE.add tbl k k;
      k
  ;;
*)
let evar (s) = he_merge (Evar (s, hash_var s));;
let emeta (e) = he_merge (Emeta (e, hash_meta e));;
let eapp (s, args) = he_merge (Eapp (s, args, hash_app s args));;
let enot (e) = he_merge (Enot (e, hash_not e));;
let eand (e1, e2) = he_merge (Eand (e1, e2, hash_and e1 e2));;
let eor (e1, e2) = he_merge (Eor (e1, e2, hash_or e1 e2));;
let eimply (e1, e2) = he_merge (Eimply (e1, e2, hash_imply e1 e2));;
let etrue = Etrue;;
let efalse = Efalse;;
let eequiv (e1, e2) = he_merge (Eequiv (e1, e2, hash_equiv e1 e2));;
let eall (v, t, e) = he_merge (Eall (v, t, e, hash_all v t e));;
let eex (v, t, e) = he_merge (Eex (v, t, e, hash_ex v t e));;
let etau (v, t, e) = he_merge (Etau (v, t, e, hash_tau v t e));;

type t = expr;;
let hash = get_hash;;
let equal = (==);;

exception Mismatch;;
exception Trivial;;

let rec xpreunify accu e1 e2 =
  match e1, e2 with
  | Evar (v1, _), Evar (v2, _) when v1 = v2 -> accu
  | Eapp (s1, a1, _), Eapp (s2, a2, _) when s1 = s2 ->
      List.fold_left2 xpreunify accu a1 a2

  (* Enot, Eand, Eor, Eimply, Eequiv, Efalse, Eall, Eex
     are not supposed to occur here *)

  | Etau _, Etau _ when equal e1 e2 -> accu

  | Emeta _, _ -> (e1, e2) :: accu
  | _, Emeta _ -> (e2, e1) :: accu
  | _, _ -> raise Mismatch
;;

let preunify e1 e2 = xpreunify [] e1 e2;;

let preunifiable e1 e2 =
  try ignore (preunify e1 e2);
      true
  with Mismatch -> false
;;

let rec occurs e f =
  if equal e f then true else begin
    match f with
    | Evar _ -> false
    | Emeta _ -> false
    | Eapp (_, args, _) -> List.exists (occurs e) args
    | Enot (g, _) -> occurs e g
    | Eand (g, h, _) -> occurs e g || occurs e h
    | Eor (g, h, _) -> occurs e g || occurs e h
    | Eimply (g, h, _) -> occurs e g || occurs e h
    | Eequiv (g, h, _) -> occurs e g || occurs e h
    | Etrue -> false
    | Efalse -> false
    | Eall (_, _, g, _) -> occurs e g
    | Eex (_, _, g, _) -> occurs e g
    | Etau (_, _, g, _) -> occurs e g
  end
;;

let rec xsize accu e =
  match e with
  | Evar _ -> accu+1
  | Emeta _ -> accu+1
  | Eapp (_, args, _) -> List.fold_left xsize accu args
  | Enot (f, _) -> xsize (accu+1) f
  | Eand (f, g, _) -> xsize (xsize (accu+1) f) g
  | Eor (f, g, _) -> xsize (xsize (accu+1) f) g
  | Eimply (f, g, _) -> xsize (xsize (accu+1) f) g
  | Eequiv (f, g, _) -> xsize (xsize (accu+1) f) g
  | Etrue -> accu+1
  | Efalse -> accu+1
  | Eall (_, _, f, _) -> xsize (accu+1) f
  | Eex (_, _, f, _) -> xsize (accu+1) f
  | Etau (_, _, f, _) -> accu+1
;;

let size e = xsize 0 e;;



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
  String.copy !cursym
;;

let make_renaming vts =
  let bijection = List.map (fun x -> (x, newvar ())) vts in
  let newvars = List.map (fun ((_,t),nv) -> (nv,t)) bijection in
  let newmap = List.map (fun ((x, _), y) -> (x, evar (y))) bijection in
  (newvars, newmap)
;;

let rec exists_fst f l =
  match l with
  | (h,_)::t when f h -> true
  | _::t -> exists_fst f t
  | [] -> false
;;

let rec var_in x = function
  | Evar (v, _) -> v = x
  | Emeta _ -> false
  | Eapp (s, args, _) -> s = x || List.exists (var_in x) args
  | Enot (e, _) -> var_in x e
  | Eand (e1, e2, _) -> var_in x e1 || var_in x e2
  | Eor (e1, e2, _) -> var_in x e1 || var_in x e2
  | Eimply (e1, e2, _) -> var_in x e1 || var_in x e2
  | Eequiv (e1, e2, _) -> var_in x e1 || var_in x e2
  | Etrue -> false
  | Efalse -> false
  | Eall (v, t, e, _) -> v = x || var_in x e
  | Eex (v, t, e, _) -> v = x || var_in x e
  | Etau (v, t, e, _) -> v = x || var_in x e
;;

let conflict v map =
  List.exists (fun (w, e) -> var_in v e) map
;;

let rec substitute map e =
  match e with
  | Evar (v, _) ->
      begin try List.assoc v map
      with Not_found -> e
      end
  | Emeta _ -> e
  | Eapp (s, args, _) ->
      assert (not (exists_fst ((=) s) map));  (* FIXME should output warning *)
      eapp (s, List.map (substitute map) args)
  | Enot (f, _) -> enot (substitute map f)
  | Eand (f, g, _) -> eand (substitute map f, substitute map g)
  | Eor (f, g, _) -> eor (substitute map f, substitute map g)
  | Eimply (f, g, _) -> eimply (substitute map f, substitute map g)
  | Eequiv (f, g, _) -> eequiv (substitute map f, substitute map g)
  | Etrue -> e
  | Efalse -> e
  | Eall (v, t, f, _) ->
      if conflict v map then
        let nv = newvar () in
        eall (nv, t, substitute ((v, evar nv) :: map) f)
      else
        eall (v, t, substitute map f)
  | Eex (v, t, f, _) ->
      if conflict v map then
        let nv = newvar () in
        eex (nv, t, substitute ((v, evar nv) :: map) f)
      else
        eex (v, t, substitute map f)
  | Etau (v, t, f, _) ->
      if conflict v map then
        let nv = newvar () in
        etau (nv, t, substitute ((v, evar nv) :: map) f)
      else
        etau (v, t, substitute map f)
;;

let rec has_meta = function
  | Evar _ -> false
  | Emeta _ -> true
  | Eapp (_, args, _) -> List.exists has_meta args
  | Enot (f, _) -> has_meta f
  | Eand (f, g, _) -> has_meta f || has_meta g
  | Eor (f, g, _) -> has_meta f || has_meta g
  | Eimply (f, g, _) -> has_meta f || has_meta g
  | Eequiv (f, g, _) -> has_meta f || has_meta g
  | Etrue -> false
  | Efalse -> false
  | Eall (_, _, f, _) -> has_meta f
  | Eex (_, _, f, _) -> has_meta f
  | Etau (_, _, f, _) -> has_meta f
;;

let rec fv_rec bvl fvl = function
  | Evar (x, _) -> if List.mem x fvl || List.mem x bvl then fvl else x :: fvl
  | Eapp (f, args, _) ->
    let nfvl = if List.mem f fvl || List.mem f bvl then fvl else f :: fvl in
    List.fold_left (fv_rec bvl) nfvl args
  | Enot (e, _) -> fv_rec bvl fvl e
  | Eand (e1, e2, _) | Eor (e1, e2, _) | Eimply (e1, e2, _)
  | Eequiv (e1, e2, _) -> let fvl1 = fv_rec bvl fvl e1 in fv_rec bvl fvl1 e2
  | Eall (x, _, e, _) | Eex(x, _, e, _) -> fv_rec (x :: bvl) fvl e
  | _ -> fvl

let free_var = fv_rec [] []

let rec type_list_rec l = function
  | Eall (_, t, e, _) | Eex(_, t, e, _) | Etau (_, t, e, _) -> 
    if List.mem t l then type_list_rec l e
    else type_list_rec (t::l) e
  | _ -> l

let type_list = type_list_rec []
