(*  Copyright 2006 INRIA  *)
Version.add "$Id: ext_induct.ml,v 1.1 2008-12-05 15:23:08 doligez Exp $";;

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

let make_match_redex e g ctx m =
  match m with
  | Eapp ("$match", Eapp (c, a, _) :: cases, _) when is_constr c ->
     let cs = List.map (make_case []) cases in
     let goodcase (c1, a1, b1) =
       c1 = "_" || c1 = c && List.length a1 = List.length a
     in
     begin try
       let (constr, args, body) = List.find goodcase cs in
       let subs =
         if constr = "_" then []
         else List.map2 (fun v x -> (v, x)) args a
       in
       let newbody = substitute subs body in
       let hyp = ctx newbody in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "match_redex", [e; hyp]);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [hyp] |];
       } ]
     with Not_found | Higher_order -> []
     end
  | Eapp ("$match", Evar (c, _) :: cases, _) when is_constr c ->
     let cs = List.map (make_case []) cases in
     let goodcase (c1, a1, b1) = a1 = [] && (c1 = c || c1 = "_") in
     begin try
       let (constr, _, body) = List.find goodcase cs in
       let hyp = ctx body in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "match_redex", [e; hyp]);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [hyp] |];
       } ]
     with Not_found | Higher_order -> []
     end
  | _ -> []
;;

let newnodes_match_redex e g =
  match e with
  | Eapp (s, [Eapp ("$match", _, _) as m; e2], _) when Eqrel.any s ->
     make_match_redex e g (fun x -> eapp (s, [x; e2])) m
  | Eapp (s, [e2; Eapp ("$match", _, _) as m], _) when Eqrel.any s ->
     make_match_redex e g (fun x -> eapp (s, [e2; x])) m
  | Enot (Eapp (s, [Eapp ("$match", _, _) as m; e2], _), _) when Eqrel.any s ->
     make_match_redex e g (fun x -> enot (eapp (s, [x; e2]))) m
  | Enot (Eapp (s, [e2; Eapp ("$match", _, _) as m], _), _) when Eqrel.any s ->
     make_match_redex e g (fun x -> enot (eapp (s, [e2; x]))) m
  | Eapp ("$match", _, _) ->
     make_match_redex e g (fun x -> x) e
  | Enot (Eapp ("$match", _, _) as m, _) ->
     make_match_redex e g (fun x -> enot (x)) m
  | _ -> []
;;

let make_match_branches ctx m =
  match m with
  | Eapp ("$match", ([] | [_]), _) ->
     Error.warn "empty pattern-matching"; raise Empty
  | Eapp ("$match", e :: cases, _) ->
      let c = normalize_cases cases in
      let f (constr, vars, body) =
        let (pattern, rvars, rbody) =
          match vars with
          | [] -> (evar (constr), [], body)
          | _ ->
             let rv = List.map (fun _ -> Expr.newvar ()) vars in
             let sub = List.map2 (fun x y -> (x, y)) vars rv in
             (eapp (constr, rv), rv, Expr.substitute sub body)
        in
        let shape = eapp ("=", [e; pattern]) in
        let ex = ex_list rvars shape in
        let f (ex, accu) v =
          match ex with
          | Eex (x, ty, b, _) ->
             let tau = etau (x, ty, b) in
             let tb = substitute [(x, tau)] b in
             (tb, (v, tau) :: accu)
          | _ -> assert false
        in
        let (taushape, subs) = List.fold_left f (ex, []) rvars in
        [taushape; (ctx (substitute subs rbody))]
      in
      List.map f c
  | _ -> assert false
;;

let get_type m =
  match m with
  | Eapp ("$match", e :: case :: _, _) ->
     let (constr, _, _) = make_case [] case in
     (Hashtbl.find constructor_table constr).cd_type
  | _ -> raise Empty
;;

let newnodes_match_cases e g =
  let mknode ctx m =
    let br = make_match_branches ctx m in
    let tycon = get_type m in
    let (args, cons) = Hashtbl.find type_table tycon in
    let tyargs = List.fold_left (fun s _ -> " _" ^ s) "" args in
    let (mctx, e1) = match m with
      | Eapp ("$match", e1 :: cases, _) ->
         let x = Expr.newvar () in
         let mctx = elam (x, sprintf "(%s%s)" tycon tyargs,
                          ctx (eapp ("$match", x :: cases)))
         in
         (mctx ,e1)
      | _ -> assert false
    in
    let ty = evar tycon in
    [ Node {
      nconc = [e];
      nrule = Ext ("induct", "cases",
                   e :: ty :: mctx :: e1 :: List.flatten br);
      nprio = Arity;
      ngoal = g;
      nbranches = Array.of_list br;
    }]
  in
  match e with
  | Eapp (s, [Eapp ("$match", _, _) as m; e2], _) when Eqrel.any s ->
     let ctx x = eapp (s, [x; e2]) in
     mknode ctx m
  | Eapp (s, [e1; Eapp ("$match", _, _) as m], _) when Eqrel.any s ->
     let ctx x = eapp (s, [e1; x]) in
     mknode ctx m
  | Enot (Eapp (s, [Eapp ("$match", _, _) as m; e2], _), _) when Eqrel.any s ->
     let ctx x = enot (eapp (s, [x; e2])) in
     mknode ctx m
  | Enot (Eapp (s, [e1; Eapp ("$match", _, _) as m], _), _) when Eqrel.any s ->
     let ctx x = enot (eapp (s, [e1; x])) in
     mknode ctx m
  | Eapp ("$match", _, _) ->
     let ctx x = x in
     mknode ctx e
  | Enot (Eapp ("$match", _, _) as m, _) ->
     let ctx x = enot (x) in
     mknode ctx m
  | _ -> []
;;

let newnodes_induction e g =
  []  (* FIXME TODO *)
;;

let newnodes_injective e g =
  match e with
  | Eapp ("=", [Eapp (f1, args1, _); Eapp (f2, args2, _)], _)
    when f1 = f2 && is_constr f1 ->
      begin try
        let ty = evar ((Hashtbl.find constructor_table f1).cd_type) in
        let branch = List.map2 (fun x y -> eapp ("=", [x; y])) args1 args2 in
        [ Node {
          nconc = [e];
          nrule = Ext ("induct", "injection", [e; ty]);
          nprio = Arity;
          ngoal = g;
          nbranches = [| branch |];
        } ]
      with Invalid_argument "List.map2" -> raise Empty
      end
  | Eapp ("=", [Eapp (f1, _, _); Eapp (f2, _, _)], _)
  | Eapp ("=", [Eapp (f1, _, _); Evar (f2, _)], _)
  | Eapp ("=", [Evar (f1, _); Eapp (f2, _, _)], _)
  | Eapp ("=", [Evar (f1, _); Evar (f2, _)], _)
    when f1 <> f2 && is_constr f1 && is_constr f2 ->
      [ Node {
        nconc = [e];
        nrule = Ext ("induct", "discriminate", [e]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| |];
      }; Stop ]
  | _ -> []
;;

let newnodes_fix e g =
  let mknode unfolded ctx fix =
    [Node {
      nconc = [e];
      nrule = Ext ("induct", "fix", [e; unfolded; ctx; fix]);
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
     with Higher_order -> []
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
     with Higher_order -> []
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
     with Higher_order -> []
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
     with Higher_order -> []
     end
  | _ -> []
;;

let newnodes e g =
  let r = newnodes_match_redex e g in
  let m =
    if r = [] then begin
      try newnodes_match_cases e g
      with Empty -> []
    end else begin
      r
    end
  in
    newnodes_fix e g
  @ m
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
  | c :: a ->
     (* TODO check type arity vs declaration *)
     (c, String.concat " " a, List.length a)
;;

let to_llproof tr_expr mlp args =
  let argl = Array.to_list args in
  let hyps = List.map fst argl in
  let add = List.flatten (List.map snd argl) in
  match mlp.mlrule with
  | Ext ("induct", "injection",
         [Eapp ("=", [Eapp (g, args1, _) as xx;
                      Eapp (_, args2, _) as yy], _) as con;
          Evar (ty, _)]) ->
     let tc = List.map tr_expr mlp.mlconc in
     let subproof =
       match hyps with
       | [sub] -> sub
       | _ -> assert false
     in
     let rec f args1 args2 i accu =
       match args1, args2 with
       | [], [] -> accu
       | a1 :: t1, a2 :: t2 ->
          let hyp = tr_expr (eapp ("=", [a1; a2])) in
          if List.exists (Expr.equal hyp) accu.conc then begin
            let (_, cons) =
              try Hashtbl.find type_table ty with Not_found -> assert false
            in
            let mk_case (name, args) =
              let params = List.map (fun _ -> Expr.newvar ()) args in
              let result = if name <> g then a1 else List.nth params i in
              let body = eapp ("$match-case", [evar (name); result]) in
              List.fold_right (fun v e -> elam (v, "?", e)) params body
            in
            let cases = List.map mk_case cons in
            let x = Expr.newvar () in
            let proj = elam (x, "?", eapp ("$match", x :: cases)) in
            let node = {
              conc = union tc (diff [hyp] accu.conc);
              rule = Rextension ("zenon_induct_f_equal",
                                 [tr_expr xx; tr_expr yy; tr_expr proj],
                                 [tr_expr con], [ [hyp] ]);
              hyps = [accu];
            } in
            f t1 t2 (i + 1) node
          end else f t1 t2 (i + 1) accu
       | _ -> assert false
     in
     (f args1 args2 0 subproof, add)
  | Ext ("induct", "injection", _) -> assert false
  | Ext ("induct", "discriminate", [e]) ->
      assert (hyps = []);
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_induct_discriminate", [], [tr_expr e], []);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("induct", "match_redex", [c; h]) ->
     let tc = tr_expr c in
     let th = tr_expr h in
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("zenon_induct_match_redex",
                          [tc; th], [tc], [ [th] ]);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "fix",
         [folded; unfolded; ctx;
          Eapp ("$fix", (Elam (f, _, (Elam (_, t, _, _) as body), _) as r)
                        :: a :: args, _)]) ->
     begin try
       let (tname, targs, ntargs) = parse_type t in
       let nx = Expr.newvar () in
       let foldx = elam (nx, "?", eapp ("$fix", [r; nx] @ args)) in
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let unfx = elam (nx, "?", List.fold_left apply xbody (nx :: args)) in
       let node = {
         conc = List.map tr_expr mlp.mlconc;
         rule = Rextension ("zenon_induct_fix",
                            List.map tr_expr [evar (tname); ctx; foldx; unfx; a],
                            [tr_expr folded],
                            [ [tr_expr unfolded] ]);
         hyps = hyps;
       } in
       (node, add)
     with Higher_order -> assert false
     end
  | Ext ("induct", "cases", c :: ty :: ctx :: m :: branches) ->
      let tc = tr_expr c in
      let tctx = tr_expr ctx in
      let tm = tr_expr m in
      let rec mk_branches l =
        match l with
        | [] -> []
        | h1 :: h2 :: t -> [tr_expr h1; tr_expr h2] :: mk_branches t
        | _ -> assert false
      in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_induct_cases", [ty; tctx; tm], [tc],
                           mk_branches branches);
        hyps = hyps;
      } in
      (node, add)
  | _ -> assert false
;;

let add_induct_def ty args constrs =
  let f i (name, a) =
    let desc = { cd_num = i; cd_type = ty; cd_args = a; cd_name = name } in
    Hashtbl.add constructor_table name desc;
  in
  list_iteri f constrs;
  Hashtbl.add type_table ty (args, constrs);
;;

let preprocess l = l;;

let add_phrase x =
  match x with
  | Hyp _ -> ()
  | Def _ -> ()
  | Sig _ -> ()
  | Inductive (ty, args, constrs) -> add_induct_def ty args constrs;
;;

let postprocess p = p;;

let add_formula e = ();;
let remove_formula e = ();;

let declare_context_coq oc =
  fprintf oc "Require Import zenon_induct.\n";
  []
;;

Extension.register {
  Extension.name = "induct";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.add_phrase = add_phrase;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
};;
