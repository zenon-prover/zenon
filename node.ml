(*  Copyright 2004 INRIA  *)
Version.add "$Id: node.ml,v 1.4 2005-11-05 11:13:17 doligez Exp $";;

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
  inst_size : node Heap.t;
  inst_front : node list;
  inst_back : node list;
};;

let compare_nodes n1 n2 =
  let get_size n =
    match n.nrule with
    | Mlproof.All (_, e) | Mlproof.NotEx (_, e) ->
        size e + 5 * count_metas e
    | _ -> assert false
  in
  get_size n1 - get_size n2
;;

let ist_small = 4;;
let ist_old = 1;;
let ist_max = ist_small + ist_old;;

let empty = {
  nullary = [];
  unary = [];
  binary = [];
  nary = [];
  inst_state = 0;
  inst_size = Heap.empty compare_nodes;
  inst_front = [];
  inst_back = [];
};;

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
            inst_size = Heap.insert q.inst_size n;
          }
      | _ -> {q with inst_back = n::q.inst_back}
      end
;;

let rec remove q =
(*
eprintf "queue: %d %d %d %d %d xx %d %d\n" (List.length q.nullary)
  (List.length q.unary) (List.length q.binary) (List.length q.nary)
  q.inst_state (List.length q.inst_front) (List.length q.inst_back);
flush stderr;
*)
  match q with
  | { nullary = h::t } -> Some (h, {q with nullary = t})
  | { unary = h::t } -> Some (h, {q with unary = t})
  | { binary = h::t } -> Some (h, {q with binary = t})
  | { nary = h::t } -> Some (h, {q with nary = t})
  | { inst_state = ist; inst_size = hp } when ist < ist_small ->
      begin match Heap.remove hp with
      | Some (h, hp) -> Some (h, {q with inst_state = ist + 1; inst_size = hp})
      | None -> remove {q with inst_state = ist_small}
      end
  | { inst_state = ist; inst_front = h::t } ->
      Some (h, {q with inst_front = t; inst_state = (ist + 1) mod ist_max})
  | { inst_back = []; inst_size = hp } ->
      if Heap.length hp = 0 then None
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
  Printf.sprintf "%d/%d/%d/%d/%d-%d" (List.length q.nullary)
                 (List.length q.unary) (List.length q.binary)
                 (List.length q.unary) (List.length q.inst_front)
                 (List.length q.inst_back)
;;
