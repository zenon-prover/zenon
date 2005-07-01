(*  Copyright 2004 INRIA  *)
Version.add "$Id: extension.ml,v 1.5 2005-07-01 12:24:47 prevosto Exp $";;

open Mlproof;;
open Printf;;

type translator =
    (Expr.expr -> Expr.expr) -> (Expr.expr -> Expr.expr)
    -> Mlproof.proof -> (Llproof.prooftree * Expr.expr list) array
    -> Llproof.prooftree * Expr.expr list
;;
type t = {
  name : string;
  newnodes : int -> Expr.expr -> Node.node_item list Lazy.t;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  to_llproof : translator;
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
    (* FIXME TODO afficher la liste des extensions disponibles *)
    raise Not_found
;;

let is_enabled name = 
  name = "core" || List.exists (fun x -> x.name = name) !active

let rec find_extension name l =
  match l with
  | [] -> assert false
  | h::_ when h.name = name -> h
  | _::t -> find_extension name t
;;

let newnodes depth e =
  List.map (fun ext -> ext.newnodes depth e) (List.rev !active)
;;

let add_formula e =
  List.iter (fun t -> t.add_formula e) !active
;;

let remove_formula e =
  List.iter (fun t -> t.remove_formula e) !active
;;

let to_llproof tr_prop tr_term node subs =
  match node.mlrule with
  | Ext (th, rule, args) ->
      let t = find_extension th !active in
      t.to_llproof tr_prop tr_term node subs
  | _ -> assert false
;;
