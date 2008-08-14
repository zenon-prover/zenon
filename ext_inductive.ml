(*  Copyright 2006 INRIA  *)
Version.add "$Id: ext_inductive.ml,v 1.4 2008-08-14 14:02:09 doligez Exp $";;

(* Extension for Coq's inductive types:
   - pattern-matching
   - injectivity
   - inductive proofs
*)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;

exception Empty;;

type constructor_desc = {
  cd_num : int;
  cd_name : string;
  cd_type : string;
  cd_args : string list;
};;

let constructor_table =
  (Hashtbl.create 100 : (string, constructor_desc) Hashtbl.t)
;;

let is_constr s = Hashtbl.mem constructor_table s;;

let rec make_cases l =
  match l with
  | Eapp (constr, vars, _) :: body :: t ->
      (constr, vars, body) :: (make_cases t)
  | [] -> []
  | _ -> Error.warn "ill-shaped pattern-matching"; raise Empty
;;

let compare_cases c1 c2 =
  let (cs1, _, _) = c1 in
  let (cs2, _, _) = c2 in
    try
      Pervasives.compare (Hashtbl.find constructor_table cs1).cd_num
                         (Hashtbl.find constructor_table cs2).cd_num
    with Not_found -> raise Empty
;;

let normalize_cases l = List.sort compare_cases (make_cases l);;

let make_match_branches ctx m =
  match m with
  | [] | [_] -> Error.warn "empty pattern-matching"; raise Empty
  | e :: cases ->
      let c = normalize_cases cases in
      let f (constr, vars, body) =
        let pattern =
          match vars with
          | [] -> evar (constr)
          | _ -> eapp (constr, vars)
        in
        let shape = eapp ("=", [e; pattern]) in
        ex_list vars (eand (shape, ctx body))
      in
      List.map f c
;;

let mkbr l = Array.map (fun x -> [x]) (Array.of_list l);;

let newnodes_match e g =
  match e with
  | Eapp ("=", [Eapp ("$match", m, _) as e1; e2], _) ->
      let branches = make_match_branches (fun x -> eapp ("=", [x; e2])) m in
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "match-eq-left", e1 :: e2 :: branches);
        nprio = Arity;
        ngoal = g;
        nbranches = mkbr branches;
      }; Stop ]
  | Eapp ("=", [e1; Eapp ("$match", m, _) as e2], _) ->
      let branches = make_match_branches (fun x -> eapp ("=", [e1; x])) m in
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "match-eq-right", e1 :: e2 :: branches);
        nprio = Arity;
        ngoal = g;
        nbranches = mkbr branches;
      }; Stop ]
  | Enot (Eapp ("=", [Eapp ("$match", m, _) as e1; e2], _), _) ->
      let branches = make_match_branches (fun x -> enot (eapp ("=", [x; e2]))) m
      in
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "match-neq-left", e1 :: e2 :: branches);
        nprio = Arity;
        ngoal = g;
        nbranches = mkbr branches;
      }; Stop ]
  | Enot (Eapp ("=", [e1; Eapp ("$match", m, _) as e2], _), _) ->
      let branches = make_match_branches (fun x -> enot (eapp ("=", [e1; x]))) m
      in
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "match-neq-right", e1 :: e2 :: branches);
        nprio = Arity;
        ngoal = g;
        nbranches = mkbr branches;
      }; Stop ]
  | Eapp ("$match", m, _) ->
      let branches = make_match_branches (fun x -> x) m in
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "match-prop", e :: branches);
        nprio = Arity;
        ngoal = g;
        nbranches = mkbr branches;
      }; Stop ]
  | _ -> []
;;

let newnodes_injective e g =
  match e with
  | Eapp ("=", [Eapp (f1, args1, _); Eapp (f2, args2, _)], _)
    when f1 = f2 && is_constr f1 ->
      begin try
        let branch = List.map2 (fun x y -> eapp ("=", [x; y])) args1 args2 in
        [ Node {
          nconc = [e];
          nrule = Ext ("inductive", "injection", [e]);
          nprio = Arity;
          ngoal = g;
          nbranches = [| branch |];
        }; Stop ]
      with Invalid_argument "List.map2" -> raise Empty
      end
  | Eapp ("=", [Eapp (f1, _, _); Eapp (f2, _, _)], _)
  | Eapp ("=", [Eapp (f1, _, _); Evar (f2, _)], _)
  | Eapp ("=", [Evar (f1, _); Eapp (f2, _, _)], _)
  | Eapp ("=", [Evar (f1, _); Evar (f2, _)], _)
    when f1 <> f2 && is_constr f1 && is_constr f2 ->
      [ Node {
        nconc = [e];
        nrule = Ext ("inductive", "discriminate", [e]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| |];
      }; Stop ]
  | _ -> []
;;

let newnodes_induction e g =
  []  (* FIXME TODO *)
;;

let newnodes e g =
    (try newnodes_match e g with Empty -> [])
  @ (try newnodes_injective e g with Empty -> [])
  @ (try newnodes_induction e g with Empty -> [])
;;

open Llproof;;

let to_llproof tr_prop tr_term mlp args =
  let argl = Array.to_list args in
  let hyps = List.map fst argl in
  let add = List.flatten (List.map snd argl) in
  match mlp.mlrule with
  | Ext ("inductive", "discriminate", [e]) ->
      let node = {
        conc = List.map tr_prop mlp.mlconc;
        rule = Rextension ("zenon_inductive_discriminate", [], [tr_prop e], []);
        hyps = [];
      } in
      (node, add)
  | Ext ("inductive", "match-neq-left", e1 :: e2 :: branches) ->
      let te1 = tr_prop e1 in
      let te2 = tr_prop e2 in
      let node = {
        conc = List.map tr_prop mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_neq_left",
                           [te1; te2],
                           [enot (eapp ("=", [te1; te2]))],
                           List.map (fun x-> [tr_prop x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-neq-right", e1 :: e2 :: branches) ->
      let te1 = tr_prop e1 in
      let te2 = tr_prop e2 in
      let node = {
        conc = List.map tr_prop mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_neq_right",
                           [te1; te2],
                           [enot (eapp ("=", [te1; te2]))],
                           List.map (fun x-> [tr_prop x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-eq-left", e1 :: e2 :: branches) ->
      let te1 = tr_prop e1 in
      let te2 = tr_prop e2 in
      let node = {
        conc = List.map tr_prop mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_eq_left",
                           [te1; te2],
                           [eapp ("=", [te1; te2])],
                           List.map (fun x-> [tr_prop x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-eq-right", e1 :: e2 :: branches) ->
      let te1 = tr_prop e1 in
      let te2 = tr_prop e2 in
      let node = {
        conc = List.map tr_prop mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_eq_right",
                           [te1; te2],
                           [eapp ("=", [te1; te2])],
                           List.map (fun x-> [tr_prop x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | _ -> assert false (* FIXME TODO *)
;;

let add_inductive_def ty constrs =
  let f i (name, args) =
    let desc = { cd_num = i; cd_type = ty; cd_args = args; cd_name = name } in
    Hashtbl.add constructor_table name desc;
  in
  list_iteri f constrs;
;;

let preprocess l =
  let f x =
    match x with
    | Hyp _ -> ()
    | Def _ -> ()
    | Sig _ -> ()
    | Inductive (ty, constrs) -> add_inductive_def ty constrs;
  in
  List.iter f l;
  l
;;

let postprocess p = p;;

let add_formula e = ();;
let remove_formula e = ();;

let declare_context_coq oc =
  fprintf oc "Require Import zenon_inductive.\n";
  []
;;

Extension.register {
  Extension.name = "inductive";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
};;
