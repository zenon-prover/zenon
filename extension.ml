(*  Copyright 2004 INRIA  *)
Version.add "$Id: extension.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

open Mlproof;;
open Printf;;

type t = {
  name : string;
  newnodes : Expr.expr -> Prio.t -> Node.node list * bool;
  add_formula : Expr.expr -> Prio.t -> unit;
  remove_formula : Expr.expr -> unit;
  to_llproof : Mlproof.proof -> Llproof.prooftree array -> Llproof.prooftree;
};;

let theories = ref ([] : t list);;
let active = ref ([] : t list);;

let register t = theories := t :: !theories;;

let activate name =
  try
    let t = List.find (fun t -> t.name = name) !theories in
    active := t :: !active;
  with Not_found ->
    eprintf "Error: extension %s does not exist\n" name;
    raise Not_found
;;

let rec find_extension name l =
  match l with
  | [] -> assert false
  | h::_ when h.name = name -> h
  | _::t -> find_extension name t
;;

let newnodes e p =
  let f (nodes, complete) t =
    if complete then (nodes, complete)
    else
      let (nodes1, complete1) = t.newnodes e p in
      (List.rev_append nodes1 nodes, complete1)
  in
  List.fold_left f ([], false) (List.rev !active)
;;

let add_formula e p =
  List.iter (fun t -> t.add_formula e p) !active
;;

let remove_formula e =
  List.iter (fun t -> t.remove_formula e) !active
;;

let to_llproof node subs =
  match node.mlrule with
  | Ext (th, rule, args) ->
      let t = find_extension th !active in
      t.to_llproof node subs
  | _ -> assert false
;;
