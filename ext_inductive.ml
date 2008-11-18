(*  Copyright 2006 INRIA  *)
Version.add "$Id: ext_inductive.ml,v 1.7 2008-11-18 12:33:29 doligez Exp $";;

(* Extension for Coq's inductive types:
   - pattern-matching
   - injectivity
   - inductive proofs
   - local fixpoint definitions
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
  cd_args : inductive_arg list;
};;

let constructor_table =
  (Hashtbl.create 100 : (string, constructor_desc) Hashtbl.t)
;;

let type_table =
  (Hashtbl.create 100 :
     (string, string list * (string * inductive_arg list) list) Hashtbl.t)
;;

let is_constr s = Hashtbl.mem constructor_table s;;

let rec make_case accu e =
  match e with
  | Eapp ("$match-case", [Evar (constr, _); body], _) ->
     (constr, List.rev accu, body)
  | Elam (v, _, body, _) ->
     make_case (v :: accu) body
  | _ -> assert false
;;

let compare_cases (cs1, _, _) (cs2, _, _) =
  try
    Pervasives.compare (Hashtbl.find constructor_table cs1).cd_num
                       (Hashtbl.find constructor_table cs2).cd_num
  with Not_found -> raise Empty
;;

let normalize_cases l = List.sort compare_cases (List.map (make_case []) l);;

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

let apply f a =
  match f with
  | Elam (v, _, body, _) -> substitute [(v, a)] body
  | _ -> raise Not_found
;;

let newnodes_fix e g =
  let mknode unfolded ctx fix =
    [Node {
      nconc = [e];
      nrule = Ext ("inductive", "fix", [e; unfolded; ctx; fix]);
      nprio = Arity;
      ngoal = g;
      nbranches = [| [unfolded] |];
    }; Stop]
  in
  match e with
  | Eapp (s, [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix;
              e1], _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "?", eapp (s, [f; e1])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Not_found -> []
     end
  | Eapp (s, [e1; Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix],
          _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "?", eapp (s, [e1; f])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Not_found -> []
     end
  | Enot (Eapp (s, [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix;
                    e1], _), _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "?", enot (eapp (s, [f; e1]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Not_found -> []
     end
  | Enot (Eapp (s, [e1;
                    Eapp ("$fix", (Elam (f, _, body, _) as r) :: args,_) as fix],
                _),_)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "?", enot (eapp (s, [e1; f]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Not_found -> []
     end
  | _ -> []
;;

let newnodes e g =
    newnodes_fix e g
  @ (try newnodes_match e g with Empty -> [])
  @ (try newnodes_injective e g with Empty -> [])
  @ (try newnodes_induction e g with Empty -> [])
;;

open Llproof;;

let rec remove_parens i j s =
  if i >= j then ""
  else if s.[i] = ' ' then remove_parens (i + 1) j s
  else if s.[j - 1] = ' ' then remove_parens i (j - 1) s
  else if s.[i] = '(' && s.[j - 1] = ')' then remove_parens (i + 1) (j - 1) s
  else String.sub s i (j - i)
;;

let remove_parens s = remove_parens 0 (String.length s) s;;

let parse_type t =
  match string_split (remove_parens t) with
  | [] -> assert false
  | c :: a -> (c, String.concat " " a, List.length a)
;;

let make_clauses t =
  try
    let (args, cstrs) = Hashtbl.find type_table t in
    let nc_name = Expr.newname () in
    let nc = evar (nc_name) in
    let h = Expr.newvar () in
    let base = elam (h, "?", elam (nc, "?", eapp (nc_name, [h]))) in
    let mklam body a =
      match a with
      | Param _ -> elam (Expr.newvar (), "?", body)
      | Self -> elam (Expr.newvar (), "?", elam (Expr.newvar (), "?", body))
    in
    let make_clause (_, ial) = List.fold_left mklam base ial in
    List.map make_clause cstrs
  with Not_found ->
    Error.err ("missing definition of type " ^ t);
    raise Exit
    (* FIXME should warn and not apply rule earlier *)
;;

let to_llproof tr_expr mlp args =
  let argl = Array.to_list args in
  let hyps = List.map fst argl in
  let add = List.flatten (List.map snd argl) in
  match mlp.mlrule with
  | Ext ("inductive", "discriminate", [e]) ->
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_inductive_discriminate", [], [tr_expr e], []);
        hyps = [];
      } in
      (node, add)
  | Ext ("inductive", "match-neq-left", e1 :: e2 :: branches) ->
      let te1 = tr_expr e1 in
      let te2 = tr_expr e2 in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_neq_left",
                           [te1; te2],
                           [enot (eapp ("=", [te1; te2]))],
                           List.map (fun x-> [tr_expr x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-neq-right", e1 :: e2 :: branches) ->
      let te1 = tr_expr e1 in
      let te2 = tr_expr e2 in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_neq_right",
                           [te1; te2],
                           [enot (eapp ("=", [te1; te2]))],
                           List.map (fun x-> [tr_expr x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-eq-left", e1 :: e2 :: branches) ->
      let te1 = tr_expr e1 in
      let te2 = tr_expr e2 in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_eq_left",
                           [te1; te2],
                           [eapp ("=", [te1; te2])],
                           List.map (fun x-> [tr_expr x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "match-eq-right", e1 :: e2 :: branches) ->
      let te1 = tr_expr e1 in
      let te2 = tr_expr e2 in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_inductive_match_eq_right",
                           [te1; te2],
                           [eapp ("=", [te1; te2])],
                           List.map (fun x-> [tr_expr x]) branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("inductive", "fix",
         [folded; unfolded; ctx;
          Eapp ("$fix", (Elam (f, _, (Elam (_, t, _, _) as body), _) as r)
                        :: a :: args,
                _) as fix]) ->
     let (tname, targs, ntargs) = parse_type t in
     let nx = Expr.newvar () in
     let h = apply ctx fix in
     let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
     let c = apply ctx (List.fold_left apply xbody (nx :: args)) in
     let p = elam (nx, "?", eimply (h, eimply (eimply (c, efalse), efalse))) in
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension (sprintf "(%s_ind %s)" tname targs,
                          p :: make_clauses tname @ [a],
                          [tr_expr folded],
                          [ [tr_expr unfolded] ]);
       hyps = hyps;
     } in
     (node, add)
  | _ -> assert false (* FIXME TODO *)
;;

let add_inductive_def ty args constrs =
  let f i (name, a) =
    let desc = { cd_num = i; cd_type = ty; cd_args = a; cd_name = name } in
    Hashtbl.add constructor_table name desc;
  in
  list_iteri f constrs;
  Hashtbl.add type_table ty (args, constrs);
;;

let preprocess l =
  let f x =
    match x with
    | Hyp _ -> ()
    | Def _ -> ()
    | Sig _ -> ()
    | Inductive (ty, args, constrs) -> add_inductive_def ty args constrs;
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
