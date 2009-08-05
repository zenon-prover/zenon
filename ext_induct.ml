(*  Copyright 2006 INRIA  *)
Version.add "$Id: ext_induct.ml,v 1.8 2009-08-05 14:47:43 doligez Exp $";;

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
let constr_head e =
  match e with
  | Eapp (s, _, _) | Evar (s, _) when is_constr s -> true
  | _ -> false
;;

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

module HE = Hashtbl.Make (Expr);;
let tblsize = 997;;
let eqs = (HE.create tblsize : expr HE.t);;
let matches = (HE.create tblsize : ((expr -> expr) * expr list) HE.t);;

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

let is_redex m =
  match m with
  | Eapp ("$match", Eapp (c, a, _) :: cases, _) when is_constr c -> true
  | Eapp ("$match", Evar (c, _) :: cases, _) when is_constr c -> true
  | _ -> false
;;

let make_match_redex e g ctx ee cases =
  let mknode c a cases =
    assert (is_constr c);
    let cs = List.map (make_case []) cases in
    let goodcase (c1, a1, b1) =
      c1 = "_" || c1 = c && List.length a1 = List.length a
    in
    try
      let (constr, args, body) = List.find goodcase cs in
      let subs =
        if constr = "_" then []
        else List.map2 (fun v x -> (v, x)) args a
      in
      let newbody = if subs = [] then body else substitute subs body in
      let hyp = ctx newbody in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "match_redex", [e; hyp]);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [hyp] |];
       } ]
    with Not_found | Higher_order -> []
  in
  match ee with
  | Eapp (c, a, _) -> mknode c a cases
  | Evar (c, _) -> mknode c [] cases
  | _ -> assert false
;;

let get_matching e =
  match e with
  | Eapp (s, [Eapp ("$match", ee :: cases, _); e2], _) when Eqrel.any s ->
     Some ((fun x -> eapp (s, [x; e2])), ee, cases)
  | Eapp (s, [e1; Eapp ("$match", ee :: cases, _)], _) when Eqrel.any s ->
     Some ((fun x -> eapp (s, [e1; x])), ee, cases)
  | Enot (Eapp (s, [Eapp ("$match", ee :: cases, _); e2], _), _)
    when Eqrel.any s ->
     Some ((fun x -> enot (eapp (s, [x; e2]))), ee, cases)
  | Enot (Eapp (s, [e1; Eapp ("$match", ee :: cases, _)], _), _)
    when Eqrel.any s ->
     Some ((fun x -> enot (eapp (s, [e1; x]))), ee, cases)
  | Eapp ("$match", ee :: cases, _) ->
     Some ((fun x -> x), ee, cases)
  | Enot (Eapp ("$match", ee :: cases, _), _) ->
     Some ((fun x -> enot (x)), ee, cases)
  (* FIXME these last two should only be done when ext_focal is active *)
  | Eapp ("Is_true", [Eapp ("$match", ee :: cases, _)], _) ->
     Some ((fun x -> eapp ("Is_true", [x])), ee, cases)
  | Enot (Eapp ("Is_true", [Eapp ("$match", ee :: cases, _)], _), _) ->
     Some ((fun x -> enot (eapp ("Is_true", [x]))), ee, cases)
  | _ -> None
;;

let make_match_branches ctx e cases =
  match cases with
  | [] -> Error.warn "empty pattern-matching"; raise Empty
  | _ ->
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
        let shape = enot (eapp ("=", [e; pattern])) in
        [enot (all_list rvars shape)]
      in
      List.map f c
;;

let rec get_match_case branches =
  match branches with
  | [] -> raise Not_found
  | [Eapp ("=", [_; e2], _) as shape; _] :: t when Index.member shape -> e2
  | _ :: t -> get_match_case t
;;

let get_type cases =
  match cases with
  | case :: _ ->
     let (constr, _, _) = make_case [] case in
     (Hashtbl.find constructor_table constr).cd_type
  | _ -> raise Empty
;;

let make_match_congruence e g ctx ee cases rhs =
  let x = Expr.newvar () in
  (* FIXME could recover the type as in mknode below *)
  let p = elam (x, "", ctx (eapp ("$match", x :: cases))) in
  [ Node {
    nconc = [e; eapp ("=", [ee; rhs])];
    nrule = CongruenceLR (p, ee, rhs);
    nprio = Arity;
    ngoal = g;
    nbranches = [| [apply p rhs] |];
  }]
;;

let newnodes_match_cases e g =
  let mknode ctx ee cases =
    let br = make_match_branches ctx ee cases in
    let tycon = get_type cases in
    let (args, cons) = Hashtbl.find type_table tycon in
    let tyargs = List.fold_left (fun s _ -> " _" ^ s) "" args in
    let x = Expr.newvar () in
    let mctx = elam (x, sprintf "(%s%s)" tycon tyargs,
                     ctx (eapp ("$match", x :: cases)))
    in
    let ty = evar tycon in
    [ Node {
      nconc = [e];
      nrule = Ext ("induct", "cases", e :: ty :: mctx :: ee :: List.flatten br);
      nprio = Arity;
      ngoal = g;
      nbranches = Array.of_list br;
    }]
  in
  match get_matching e with
  | Some (ctx, ee, cases) when constr_head ee ->
     make_match_redex e g ctx ee cases
  | Some (ctx, ee, cases) ->
     begin try
       make_match_congruence e g ctx ee cases (HE.find eqs ee)
     with Not_found ->
       mknode ctx ee cases
     end
  | None -> []
;;

let newnodes_match_cases_eq e g =
  match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 ->
     let mknode (ctx, cases) =
       let x = Expr.newvar () in
       let p = elam (x, "", ctx (eapp ("$match", x :: cases))) in
       Node {
         nconc = [apply p e1; e];
         nrule = CongruenceLR (p, e1, e2);
         nprio = Arity;
         ngoal = g;
         nbranches = [| [apply p e2] |];
       }
     in
     List.map mknode (HE.find_all matches e1)
  | _ -> []
;;

let make_induction_branch ty p (con, args) =
  let rec f vars args =
    match args with
    | Param s :: t ->
       let x = Expr.newvar () in
       eall (x, s, f (x :: vars) t)
    | Self :: t ->
       let x = Expr.newvar () in
       eall (x, ty, eimply (apply p x, f (x :: vars) t))
    | [] ->
       let v = if vars = [] then evar (con) else eapp (con, List.rev vars) in
       apply p v
  in
  [enot (f [] args)]
;;

let newnodes_induction e g =
  match e with
  | Enot (Eall (_, "", _, _), _) -> []
  | Enot (Eall (v, ty, body, _), _) ->
     begin try
       let (tycon, _, _) = parse_type ty in
       let (args, cons) = Hashtbl.find type_table tycon in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty p) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_notall",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | Eex (_, "", _, _) -> []
  | Eex (v, ty, Enot (body, _), _) ->
     begin try
       let (tycon, _, _) = parse_type ty in
       let (args, cons) = Hashtbl.find type_table tycon in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty p) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_exnot",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | Eex (v, ty, body, _) ->
     begin try
       let (tycon, _, _) = parse_type ty in
       let (args, cons) = Hashtbl.find type_table tycon in
       let np = elam (v, ty, enot (body)) in
       let p = elam (v, ty, body) in
       let br = List.map (make_induction_branch ty np) cons in
       [ Node {
         nconc = [e];
         nrule = Ext ("induct", "induction_ex",
                      e :: evar (tycon) :: p :: List.flatten br);
         nprio = Inst e;
         nbranches = Array.of_list br;
         ngoal = g;
       }]
     with Not_found -> []
     end
  | _ -> []
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
      nprio = Inst e;
      ngoal = g;
      nbranches = [| [unfolded] |];
    }; Stop]
  in
  match e with
  | Eapp ("Is_true",
          [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix], _) ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", eapp ("Is_true", [f])) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Enot (Eapp ("Is_true",
                [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix],
                _), _) ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", enot (eapp ("Is_true", [f]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | Eapp (s, [Eapp ("$fix", (Elam (f, _, body, _) as r) :: args, _) as fix;
              e1], _)
    when Eqrel.any s ->
     begin try
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let e2 = List.fold_left apply xbody args in
       let ctx = elam (f, "", eapp (s, [f; e1])) in
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
       let ctx = elam (f, "", eapp (s, [e1; f])) in
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
       let ctx = elam (f, "", enot (eapp (s, [f; e1]))) in
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
       let ctx = elam (f, "", enot (eapp (s, [e1; f]))) in
       let unfolded = apply ctx e2 in
       mknode unfolded ctx fix
     with Higher_order -> []
     end
  | _ -> []
;;

let newnodes e g =
    newnodes_fix e g
  @ (try newnodes_match_cases e g with Empty -> [])
  @ (try newnodes_match_cases_eq e g with Empty -> [])
  @ (try newnodes_injective e g with Empty -> [])
  @ (try newnodes_induction e g with Empty -> [])
;;

open Llproof;;

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
              List.fold_right (fun v e -> elam (v, "", e)) params body
            in
            let cases = List.map mk_case cons in
            let x = Expr.newvar () in
            let proj = elam (x, "", eapp ("$match", x :: cases)) in
            let node = {
              conc = union tc (diff accu.conc [hyp]);
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
                          [tc], [tc], [ [th] ]);
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
       let foldx = elam (nx, "", eapp ("$fix", [r; nx] @ args)) in
       let xbody = substitute_2nd [(f, eapp ("$fix", [r]))] body in
       let unfx = elam (nx, "", List.fold_left apply xbody (nx :: args)) in
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
      let listify x = [tr_expr x] in
      let node = {
        conc = List.map tr_expr mlp.mlconc;
        rule = Rextension ("zenon_induct_cases", [ty; tctx; tm], [tc],
                           List.map listify branches);
        hyps = hyps;
      } in
      (node, add)
  | Ext ("induct", "induction_notall", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let node = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("zenon_induct_induction_notall",
                          [ty; tp], [tc], List.map listify branches);
       hyps = hyps;
     } in
     (node, add)
  | Ext ("induct", "induction_exnot", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let c0 =
       match p with
       | Elam (v, tyv, body, _) -> enot (eall (v, tyv, body))
       | _ -> assert false
     in
     let conc0 = c0 :: (Expr.diff mlp.mlconc [c]) in
     let n0 = {
       conc = List.map tr_expr conc0;
       rule = Rextension ("zenon_induct_induction_notall",
                          [ty; tp], [tr_expr c0], List.map listify branches);
       hyps = hyps;
     } in
     let n1 = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("zenon_induct_allexnot", [ty; tp], [tc], [[c0]]);
       hyps = [n0];
     } in
     (n1, add)
  | Ext ("induct", "induction_ex", c :: ty :: p :: branches) ->
     let tc = tr_expr c in
     let tp = tr_expr p in
     let listify x = [tr_expr x] in
     let (c0, np) =
       match p with
       | Elam (v, tyv, body, _) ->
          (enot (eall (v, tyv, enot (body))), elam (v, tyv, enot (body)))
       | _ -> assert false
     in
     let tnp = tr_expr np in
     let conc0 = c0 :: (Expr.diff mlp.mlconc [c]) in
     let n0 = {
       conc = List.map tr_expr conc0;
       rule = Rextension ("zenon_induct_induction_notall",
                          [ty; tnp], [tr_expr c0], List.map listify branches);
       hyps = hyps;
     } in
     let n1 = {
       conc = List.map tr_expr mlp.mlconc;
       rule = Rextension ("zenon_induct_allnotex", [ty; tp], [tc], [[c0]]);
       hyps = [n0];
     } in
     (n1, add)
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

let add_formula e =
  match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 -> HE.add eqs e1 e2
  | _ ->
    match get_matching e with
    | Some (ctx, ee, cases) when not (constr_head ee) ->
        HE.add matches ee (ctx, cases)
    | _ -> ()
;;

let remove_formula e =
  match e with
  | Eapp ("=", [e1; e2], _) when constr_head e2 -> HE.remove eqs e1
  | _ ->
    match get_matching e with
    | Some (ctx, ee, cases) when not (constr_head ee) ->
       HE.remove matches ee
    | _ -> ()
;;

let declare_context_coq oc =
  fprintf oc "Require Import zenon_induct.\n";
;;

let predef () = [];;

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
  Extension.predef = predef;
};;
