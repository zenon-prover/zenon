(*  Copyright 2004 INRIA  *)
Version.add "$Id: extension.ml,v 1.12 2009-07-16 12:06:34 doligez Exp $";;

open Mlproof;;
open Printf;;

type translator =
    (Expr.expr -> Expr.expr) ->
    Mlproof.proof -> (Llproof.prooftree * Expr.expr list) array ->
    Llproof.prooftree * Expr.expr list
;;
type t = {
  name : string;
  newnodes : Expr.expr -> int -> Node.node_item list;
  add_formula : Expr.expr -> unit;
  remove_formula : Expr.expr -> unit;
  preprocess : Phrase.phrase list -> Phrase.phrase list;
  add_phrase : Phrase.phrase -> unit;
  postprocess : Llproof.proof -> Llproof.proof;
  to_llproof : translator;
  declare_context_coq : out_channel -> unit;
  predef : unit -> string list;
};;

let theories = ref ([] : t list);;
let active = ref ([] : t list);;

let register t = theories := t :: !theories;;

let activate name =
  try
    let t = List.find (fun t -> t.name = name) !theories in
    active := t :: !active;
  with Not_found ->
    Error.err (sprintf "no extension named %s" name);
    Error.err "The following extensions are available";
    List.iter (fun e -> Error.err e.name) !theories;
    raise Not_found;
;;

let is_active name = List.exists (fun x -> x.name = name) !active;;

let rec find_extension name l =
  match l with
  | [] -> assert false
  | h::_ when h.name = name -> h
  | _::t -> find_extension name t
;;

let newnodes e g =
  List.map (fun ext -> ext.newnodes e g) (List.rev !active)
;;

let add_formula e =
  List.iter (fun t -> t.add_formula e) !active
;;

let remove_formula e =
  List.iter (fun t -> t.remove_formula e) !active
;;

let preprocess l =
  List.fold_left (fun hyps ext -> ext.preprocess hyps) l (List.rev !active)
;;

let add_phrase p =
  List.iter (fun ext -> ext.add_phrase p) (List.rev !active)
;;

let postprocess p =
  List.fold_left (fun prf ext -> ext.postprocess prf) p !active
;;

let to_llproof tr_expr node subs =
  match node.mlrule with
  | Ext (th, rule, args) ->
      let t = find_extension th !active in
      t.to_llproof tr_expr node subs
  | _ -> assert false
;;

let declare_context_coq oc =
  List.iter (fun ext -> ext.declare_context_coq oc) !active
;;

let predef () =
  List.flatten (["="] :: List.map (fun ext -> ext.predef ()) !active)
;;
