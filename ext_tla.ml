(*  Copyright 2008 INRIA  *)
Version.add "$Id: ext_tla.ml,v 1.4 2008-09-09 15:09:16 doligez Exp $";;

(* Extension for TLA+ : set theory. *)
(* Symbols: TLA.in *)

open Printf;;

open Expr;;
open Misc;;
open Mlproof;;
open Node;;
open Phrase;;

let add_formula e = ();;
let remove_formula e = ();;

let tla_set_constructors = [
  "TLA.emptyset";
  "TLA.upair";
  "TLA.add";
  "TLA.infinity";
  "TLA.SUBSET";
  "TLA.UNION";
  "TLA.INTER";
  "TLA.cup";
  "TLA.cap";
  "TLA.setminus";
  "TLA.subsetOf";
  "TLA.setOfAll";
];;

let is_set_expr e =
  match e with
  | Evar (v, _) -> List.mem v tla_set_constructors
  | Eapp (f, _, _) -> List.mem f tla_set_constructors
  | _ -> false
;;

let newnodes e g =
  match e with
  | Eapp ("TLA.in",
          [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
          _) ->
      let branches = [| [eapp ("TLA.in", [e1; s]);
                         substitute [(v, e1)] p;
                        ] |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "in_subsetof", [e1; s; pred]);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }]
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
                _), _) ->
      let branches = [| [enot (eapp ("TLA.in", [e1; s]))];
                        [enot (substitute [(v, e1)] p)];
                     |] in
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "notin_subsetof", [e1; s; pred]);
        nprio = Arity;
        ngoal = g;
        nbranches = branches;
      }]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _) ->
     let branches = [| [eapp ("TLA.subseteq", [e1; s])] |] in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_SUBSET", [e1; s]);
       nprio = Arity;
       ngoal = g;
       nbranches = branches;
     }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _), _) ->
     let branches = [| [enot (eapp ("TLA.subseteq", [e1; s]))] |] in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notin_SUBSET", [e1; s]);
       nprio = Arity;
       ngoal = g;
       nbranches = branches;
     }]
  | Eapp ("=", [e1; e2], _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let branches = [| [eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                             eapp ("TLA.in", [x; e2])))] |]
     in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "extensionality", [e1; e2]);
       nprio = Inst e;
       ngoal = g;
       nbranches = branches;
     }]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let branches = [| [enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                                   eapp ("TLA.in", [x; e2]))))
                    ] |]
     in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notextensionality", [e1; e2]);
       nprio = Inst e;
       ngoal = g;
       nbranches = branches;
     }]
  | _ -> []
;;


let to_llargs tr_prop tr_term r =
  match r with
  | Ext (_, "in_subsetof", [e1; s; Elam (v, _, p, _) as pred]) ->
      let h1 = tr_prop (eapp ("TLA.in", [e1; s])) in
      let h2 = tr_prop (substitute [(v, e1)] p) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.subsetOf", [s; pred])]))
      in
      ("zenon_in_subsetof", [tr_term e1; tr_term s; tr_term pred],
       [c], [ [h1; h2] ])
  | Ext (_, "notin_subsetof", [e1; s; Elam (v, _, p, _) as pred]) ->
      let h1 = tr_prop (enot (eapp ("TLA.in", [e1; s]))) in
      let h2 = tr_prop (enot (substitute [(v, e1)] p)) in
      let c = tr_prop (enot (eapp ("TLA.in",
                                   [e1; eapp ("TLA.subsetOf", [s; pred])])))
      in
      ("zenon_notin_subsetof", [tr_term e1; tr_term s; tr_term pred],
       [c], [ [h1]; [h2] ])
  | Ext (_, "in_SUBSET", [e1; s]) ->
      let h1 = tr_prop (eapp ("TLA.subseteq", [e1; s])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.SUBSET", [s])])) in
      ("zenon_in_SUBSET", [tr_term e1; tr_term s], [c], [[h1]])
  | Ext (_, "notin_SUBSET", [e1; s]) ->
      let h1 = tr_prop (enot (eapp ("TLA.subseteq", [e1; s]))) in
      let c = tr_prop (enot (eapp ("TLA.in", [e1; eapp ("TLA.SUBSET", [s])]))) in
      ("zenon_notin_SUBSET", [tr_term e1; tr_term s], [c], [[h1]])
  | Ext (_, "extensionality", [e1; e2]) ->
      let x = Expr.newvar () in
      let h1 = tr_prop (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                             eapp ("TLA.in", [x; e2]))))
      in
      let c = tr_prop (eapp ("=", [e1; e2])) in
      ("zenon_extensionality", [tr_term e1; tr_term e2], [c], [[h1]])
  | Ext (_, "notextensionality", [e1; e2]) ->
      let x = Expr.newvar () in
      let h1 = tr_prop (enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                                   eapp ("TLA.in", [x; e2])))))
      in
      let c = tr_prop (enot (eapp ("=", [e1; e2]))) in
      ("zenon_notextensionality", [tr_term e1; tr_term e2], [c], [[h1]])
  | _ -> assert false
;;

let to_llproof tr_prop tr_term mlp args =
  let (name, meta, con, hyp) = to_llargs tr_prop tr_term mlp.mlrule in
  let (subs, exts) = List.split (Array.to_list args) in
  let ext = List.fold_left Expr.union [] exts in
  let extras = Expr.diff ext mlp.mlconc in
  let nn = {
      Llproof.conc = List.map tr_prop (extras @@ mlp.mlconc);
      Llproof.rule = Llproof.Rextension (name, meta, con, hyp);
      Llproof.hyps = subs;
    }
  in (nn, extras)
;;

let preprocess l = l;;

let postprocess p = p;;

let declare_context_coq oc =
  [
    "TLA.in"; "TLA.subsetOf";
  ]
;;

Extension.register {
  Extension.name = "tla";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
};;
