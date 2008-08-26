(*  Copyright 2008 INRIA  *)
Version.add "$Id: ext_tla.ml,v 1.1 2008-08-26 13:47:41 doligez Exp $";;

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

let newnodes e g =
  match e with
  | Eapp ("TLA.in",
          [e1; Eapp ("subsetOf", [s; Elam (v, _, p, _) as pred], _)],
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
                [e1; Eapp ("subsetOf", [s; Elam (v, _, p, _) as pred], _)],
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
  | _ -> []
;;


let to_llargs tr_prop tr_term r =
  match r with
  | Ext (_, "in_subsetof", [e1; s; Elam (v, _, p, _) as pred]) ->
      let h1 = tr_prop (eapp ("TLA.in", [e1; s])) in
      let h2 = tr_prop (substitute [(v, e1)] p) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.subsetOf", [s; pred])]))
      in
      ("subsetOfE", [tr_term e1; tr_term s; tr_term pred; tr_term efalse],
       [c], [ [h1; h2] ])
  | Ext (_, "notin_subsetof", [e1; s; Elam (v, _, p, _) as pred]) ->
      let h1 = tr_prop (enot (eapp ("TLA.in", [e1; s]))) in
      let h2 = tr_prop (enot (substitute [(v, e1)] p)) in
      let c = tr_prop (enot (eapp ("TLA.in",
                                   [e1; eapp ("TLA.subsetOf", [s; pred])])))
      in
      ("zenon_notin_subsetof", [tr_term e1; tr_term s; tr_term pred],
       [c], [ [h1]; [h2] ])
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
