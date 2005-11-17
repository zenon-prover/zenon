(*  Copyright 2004 INRIA  *)
Version.add "$Id: node.ml,v 1.8 2005-11-17 12:39:07 doligez Exp $";;

open Expr;;
open Printf;;

type priority =
  | Arity
  | Inst of int
;;

type node = {
  nconc : expr list;
  nrule : Mlproof.rule;
  nprio : priority;
  ngoal : int;
  nbranches : expr list array;
};;

type node_item =
  | Node of node
  | Stop
;;

let rec xrelevant cur l accu =
  match cur, l with
  | [], h :: t -> xrelevant h t accu
  | (Node n :: t1), t -> xrelevant t1 t (n :: accu)
  | (Stop :: _), _ -> (List.rev accu, true)
  | [], [] -> (List.rev accu, false)
;;

let relevant l = xrelevant [] l [];;


(* first draft: use stacks for finite nodes, and a pseudo-FIFO
   for the instantiation nodes
   TODO: efficient FIFO
*)

type queue = {
  nullary : node list;
  unary : node list;
  binary : node list;
  nary : node list;
  inst_state : int;
  inst_size : (int * node Heap.t) list;
  inst_front : node list;
  inst_back : node list;
};;

let k_meta_mul = 5;;
let k_tau_div = 5;;

let use_goalness = true;;
let ist_small = 16;;         (* ist_small must be even *)
let ist_old = 2;;
let ist_max = ist_small + ist_old;;

let compare_nodes n1 n2 =
  let get_size n =
    match n.nrule with
    | Mlproof.All (_, e) | Mlproof.NotEx (_, e) ->
        size e + count_metas e * k_meta_mul + get_taus e / k_tau_div
    | _ -> assert false
  in
  get_size n1 - get_size n2
;;

let empty = {
  nullary = [];
  unary = [];
  binary = [];
  nary = [];
  inst_state = 0;
  inst_size = [];
  inst_front = [];
  inst_back = [];
};;

let insert_by_goalness l n =
  let gness = if use_goalness then n.ngoal else 0 in
  let h = try List.assoc gness l with Not_found -> Heap.empty compare_nodes in
  let nh = Heap.insert h n in
  let rec list_insert i e l =
    match l with
    | [] -> [(i, e)]
    | (j, _) :: t when j = i -> (i, e) :: t
    | (j, _) :: _ when j > i -> (i, e) :: l
    | h::t -> h :: (list_insert i e t)
  in
  list_insert gness nh l
;;

let insert q n =
  match n.nprio with
  | Arity ->
      begin match Array.length n.nbranches with
      | 0 -> {q with nullary = n::q.nullary}
      | 1 -> {q with unary = n::q.unary}
      | 2 -> {q with binary = n::q.binary}
      | _ -> {q with nary = n::q.nary}
      end
  | Inst _ ->
      begin match n.nrule with
      | Mlproof.All _ | Mlproof.NotEx _ ->
          { q with
            inst_back = n::q.inst_back;
            inst_size = insert_by_goalness q.inst_size n;
          }
      | _ -> {q with inst_back = n::q.inst_back}
      end
;;

let remove_by_goalness ist l =
  let rec remove_at i l =
    match l with
    | [] -> None
    | (j, h) :: t when j < i ->
        begin match remove_at i t with
        | None -> None
        | Some (x, nl) -> Some (x, (j,h)::nl)
        end
    | (j, h) :: t ->
        begin match Heap.remove h with
        | None -> remove_at i t
        | Some (x, nh) -> Some (x, (j,nh)::t)
        end
  in
  if ist mod 2 = 0 then begin
    remove_at 0 l
  end else begin
    let better r1 r2 =
      match r1, r2 with
      | None, _ -> false
      | _, None -> true
      | Some n1, Some n2 -> compare_nodes n1 n2 < 0
    in
    let rec find_best i hd l =
      match l with
      | [] -> i
      | (j, h) :: t ->
          let hd2 = Heap.head h in
          if better hd2 hd
          then find_best j hd2 t
          else find_best i hd t
    in
    remove_at (find_best 0 None l) l
  end
;;

let rec is_empty l =
  match l with
  | [] -> true
  | (i, h) :: t -> Heap.is_empty h && is_empty t
;;

let rec remove q =
  match q with
  | { nullary = h::t } -> Some (h, {q with nullary = t})
  | { unary = h::t } -> Some (h, {q with unary = t})
  | { binary = h::t } -> Some (h, {q with binary = t})
  | { nary = h::t } -> Some (h, {q with nary = t})
  | { inst_state = ist; inst_size = hpl } when ist < ist_small ->
      begin match remove_by_goalness ist hpl with
      | Some (x, l) -> Some (x, {q with inst_state = ist + 1; inst_size = l})
      | None -> remove {q with inst_state = ist_small}
      end
  | { inst_state = ist; inst_front = h::t } ->
      Some (h, {q with inst_front = t; inst_state = (ist + 1) mod ist_max})
  | { inst_back = []; inst_size = hpl } ->
      if is_empty hpl then None
      else remove {q with inst_state = 0}
  | { inst_back = l } -> remove {q with inst_front = List.rev l; inst_back = []}
;;

let rec last x l =
  match l with
  | [] -> x
  | h::t -> last h t
;;

let head q =
  match q with
  | { nullary = h::t } -> Some h
  | { unary = h::t } -> Some h
  | { binary = h::t } -> Some h
  | { nary = h::t } -> Some h
  | { inst_front = h::t} -> Some h
  | { inst_back = h::t} -> Some (last h t)
  | _ -> None
;;

let size q =
  sprintf "%d/%d/%d/%d/%d-%d" (List.length q.nullary)
          (List.length q.unary) (List.length q.binary)
          (List.length q.unary) (List.length q.inst_front)
          (List.length q.inst_back)
;;
