(*  Copyright 2001 INRIA  *)
Misc.version "$Id: heap.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

type 'a tree =
  | Node of 'a * 'a tree * 'a tree
  | Leaf
;;

type 'a t = {
  cmp : 'a -> 'a -> int;
  tree : 'a tree;
};;

let empty cmp = {
  cmp = cmp;
  tree = Leaf;
};;

module Rnd = Random.State;;
let rnd = Rnd.make [| 234; 45362; 3451314; 9780709 |];;

let rec insert_aux cmp t x =
  match t with
  | Leaf -> Node (x, Leaf, Leaf)
  | Node (y, b1, b2) ->
     let (nb1, nb2) = if Rnd.bool rnd then (b1, b2) else (b2, b1) in
     if cmp x y <= 0
     then Node (x, insert_aux cmp nb1 y, nb2)
     else Node (y, insert_aux cmp nb1 x, nb2)
;;

let insert hp x = {
  cmp = hp.cmp;
  tree = insert_aux hp.cmp hp.tree x;
};;

let rec remove_aux cmp t =
  match t with
  | Leaf -> None
  | Node (y, Leaf, b2) -> Some (y, b2)
  | Node (y, b1, Leaf) -> Some (y, b1)
  | Node (y, (Node (z1, _, _) as b1), (Node (z2, _, _) as b2)) ->
     let (nb1, nb2) = if cmp z1 z2 < 0 then (b1, b2) else (b2, b1) in
     match remove_aux cmp nb1 with
     | Some (nz1, nnb1) -> Some (y, Node (nz1, nnb1, nb2))
     | None -> assert false
;;

let remove hp =
  match remove_aux hp.cmp hp.tree with
  | Some (x, newtree) -> Some (x, { cmp = hp.cmp; tree = newtree })
  | None -> None
;;

let head hp =
  match hp.tree with
  | Leaf -> None
  | Node (y, _, _) -> Some y
;;

let rec length_aux = function
  | Leaf -> 0
  | Node (_, b1, b2) -> 1 + length_aux b1 + length_aux b2
;;

let length hp = length_aux hp.tree;;

let rec iter_aux f = function
  | Leaf -> ()
  | Node (x, b1, b2) -> f x; iter_aux f b1; iter_aux f b2;
;;

let iter f hp = iter_aux f hp.tree;;
