(*  Copyright 2008 INRIA  *)
Version.add "$Id: ext_tla.ml,v 1.12 2008-10-20 16:30:42 doligez Exp $";;

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
  "TLA.FuncSet";
];;

let is_set_expr e =
  match e with
  | Evar (v, _) -> List.mem v tla_set_constructors
  | Eapp (f, _, _) -> List.mem f tla_set_constructors
  | _ -> false
;;

let tla_fcn_constructors = [
  "TLA.Fcn";
  "TLA.except";
  "TLA.oneArg";
  "TLA.extend";
];;

let is_fcn_expr e =
  match e with
  | Evar (v, _) -> List.mem v tla_fcn_constructors
  | Eapp (f, _, _) -> List.mem f tla_fcn_constructors
  | _ -> false
;;

let newnodes_prop e g =
  match e with
  | Eapp ("TLA.in", [e1; Evar ("TLA.emptyset", _)], _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_emptyset", [e1]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| |];
     }]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_upair", [e1; e2; e3]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [eapp ("=", [e1; e2])];
                      [eapp ("=", [e1; e3])] |];
     }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _), _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notin_upair", [e1; e2; e3]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [enot (eapp ("=", [e1; e2])); enot (eapp ("=", [e1; e3]))]
                   |];
     }]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.add", [e2; e3], _)], _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_add", [e1; e2; e3]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [eapp ("=", [e1; e2])];
                      [eapp ("TLA.in", [e1; e3])] |];
     }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.add", [e2; e3], _)], _), _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notin_add", [e1; e2; e3]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [enot (eapp ("=", [e1; e2]));
                       enot (eapp ("TLA.in", [e1; e3]))] |];
     }]
  (* infinity -- needed ? *)
  | Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_SUBSET", [e1; s]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [eapp ("TLA.subseteq", [e1; s])] |];
     }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _), _) ->
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notin_SUBSET", [e1; s]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [enot (eapp ("TLA.subseteq", [e1; s]))] |];
     }]
  (* UNION *)
  (* INTER *)
  | Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "in_cup", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [eapp ("TLA.in", [e1; e2])];
                       [eapp ("TLA.in", [e1; e3])] |];
      }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _), _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "notin_cup", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [enot (eapp ("TLA.in", [e1; e2]));
                        enot (eapp ("TLA.in", [e1; e3]))] |];
      }]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "in_cap", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [eapp ("TLA.in", [e1; e2]);
                        eapp ("TLA.in", [e1; e3])] |];
      }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _), _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "notin_cap", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [enot (eapp ("TLA.in", [e1; e2]))];
                       [enot (eapp ("TLA.in", [e1; e3]))] |];
      }]
  | Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "in_setminus", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [eapp ("TLA.in", [e1; e2]);
                        enot (eapp ("TLA.in", [e1; e3]))] |];
      }]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _), _) ->
      [ Node {
        nconc = [e];
        nrule = Ext ("tla", "notin_setminus", [e1; e2; e3]);
        nprio = Arity;
        ngoal = g;
        nbranches = [| [enot (eapp ("TLA.in", [e1; e2]))];
                       [eapp ("TLA.in", [e1; e3])] |];
      }]
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
  (* setOfAll *)
  | Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _) ->
     let h1 = eapp ("TLA.isAFcn", [f]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]) in
     let x = Expr.newvar () in
     let h3 = eall (x, "",
                eimply (eapp ("TLA.in", [x; a]),
                        eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
     in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "in_funcset", [f; a; b]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [h1; h2; h3] |];
     }]
  | Enot (Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _), _) ->
     let h1 = eapp ("TLA.isAFcn", [f]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f])]) in
     let x = Expr.newvar () in
     let h3 = eall (x, "",
                eimply (eapp ("TLA.in", [x; a]),
                        eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
     in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notin_funcset", [f; a; b]);
       nprio = Arity;
       ngoal = g;
       nbranches = [| [enot h1]; [enot h2]; [enot h3] |];
     }]
  | Eapp ("=", [e1; e2], _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "setext", [e1; e2]);
       nprio = Inst e;
       ngoal = g;
       nbranches = [| [eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                            eapp ("TLA.in", [x; e2])))] |];
     }]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "notsetext", [e1; e2]);
       nprio = Inst e;
       ngoal = g;
       nbranches = [| [enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                                  eapp ("TLA.in", [x; e2]))))]
                   |];
     }]
  | Eapp ("=", [e1; e2], _) when is_fcn_expr e1 || is_fcn_expr e2 ->
     let x = Expr.newvar () in
     [ Node {
       nconc = [e];
       nrule = Ext ("tla", "funext", [e1; e2]);
       nprio = Inst e;
       ngoal = g;
       nbranches = [| [eall (x, "", eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                                eapp ("TLA.fapply", [e2; x])]))]
                   |];
     }]
  (* TODO : notfunext -- with a lot more hypotheses *)
  | _ -> []
;;

(*
let newnodes_rewrite e =
  match e with
  | Eapp ("TLA.fapply", [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _); a], _)
  -> let x = Expr.newvar () in
     let fres = Expr.substitute [(v, a)] b in
     ([s; l; a], eapp ("TLA.in", [a; s]), fres)
  | Eapp ("TLA.fapply", [Eapp ("TLA.except", [fn; arg; val])])
...
*)

let newnodes_expr e g =
  let mknode rule branches =
    [ Node {
      nconc = [e];
      nrule = rule;
      nprio = Arity;
      ngoal = g;
      nbranches = branches;
    }]
  in
  match e with
  | Eapp ("=",
          [Eapp ("TLA.fapply",
                 [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _);
                  a], _);
           e2], _) ->
     let x = Expr.newvar () in
     let ctx = elam (x, "", eapp ("=", [x; e2])) in
     let fres = Expr.substitute [(v, a)] b in
     mknode (Ext ("tla", "fapplyfcn", [ctx; s; l; a]))
            [| [enot (eapp ("TLA.in", [a; s]))];
               [eapp ("=", [fres; e2])] |]
  | Eapp ("=",
          [e1;
           Eapp ("TLA.fapply",
                 [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _);
                  a], _)], _) ->
     let x = Expr.newvar () in
     let ctx = elam (x, "", eapp ("=", [e1; x])) in
     let fres = Expr.substitute [(v, a)] b in
     mknode (Ext ("tla", "fapplyfcn", [ctx; s; l; a]))
            [| [enot (eapp ("TLA.in", [a; s]))];
               [eapp ("=", [e1; fres])] |]
  | Enot (Eapp ("=",
                [Eapp ("TLA.fapply",
                       [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _);
                        a], _);
                 e2], _), _) ->
     let x = Expr.newvar () in
     let ctx = elam (x, "", enot (eapp ("=", [x; e2]))) in
     let fres = Expr.substitute [(v, a)] b in
     mknode (Ext ("tla", "fapplyfcn", [ctx; s; l; a]))
            [| [enot (eapp ("TLA.in", [a; s]))];
               [enot (eapp ("=", [fres; e2]))] |]
  | Enot (Eapp ("=",
                [e1;
                 Eapp ("TLA.fapply",
                       [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _);
                        a], _)], _), _) ->
     let x = Expr.newvar () in
     let ctx = elam (x, "", enot (eapp ("=", [e1; x]))) in
     let fres = Expr.substitute [(v, a)] b in
     mknode (Ext ("tla", "fapplyfcn", [ctx; s; l; a]))
            [| [enot (eapp ("TLA.in", [a; s]))];
               [enot (eapp ("=", [e1; fres]))] |]
  | _ -> []
;;

let newnodes e g =
  newnodes_prop e g @ newnodes_expr e g
;;

let to_llargs tr_prop tr_term r =
  match r with
  | Ext (_, "in_emptyset", [e1]) ->
     let c = tr_prop (eapp ("TLA.in", [e1; evar ("TLA.emptyset")])) in
      ("zenon_in_emptyset", [tr_term e1], [c], [])
  | Ext (_, "in_upair", [e1; e2; e3]) ->
      let h1 = tr_prop (eapp ("=", [e1; e2])) in
      let h2 = tr_prop (eapp ("=", [e1; e3])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.upair", [e2; e3])])) in
      ("zenon_in_upair", List.map tr_term [e1; e2; e3], [c], [[h1]; [h2]])
  | Ext (_, "notin_upair", [e1; e2; e3]) ->
      let h1 = tr_prop (enot (eapp ("=", [e1; e2]))) in
      let h2 = tr_prop (enot (eapp ("=", [e1; e3]))) in
      let c = tr_prop (enot (eapp ("TLA.in",
                                   [e1; eapp ("TLA.upair", [e2; e3])])))
      in
      ("zenon_notin_upair", List.map tr_term [e1; e2; e3], [c], [[h1; h2]])
  | Ext (_, "in_add", [e1; e2; e3]) ->
      let h1 = tr_prop (eapp ("=", [e1; e2])) in
      let h2 = tr_prop (eapp ("TLA.in", [e1; e3])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.add", [e2; e3])])) in
      ("zenon_in_add", List.map tr_term [e1; e2; e3], [c], [[h1]; [h2]])
  | Ext (_, "notin_add", [e1; e2; e3]) ->
      let h1 = tr_prop (enot (eapp ("=", [e1; e2]))) in
      let h2 = tr_prop (enot (eapp ("TLA.in", [e1; e3]))) in
      let c = tr_prop (enot (eapp ("TLA.in", [e1; eapp ("TLA.add", [e2; e3])])))
      in
      ("zenon_notin_add", List.map tr_term [e1; e2; e3], [c], [[h1; h2]])
  (* infinity *)
  | Ext (_, "in_SUBSET", [e1; s]) ->
      let h1 = tr_prop (eapp ("TLA.subseteq", [e1; s])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.SUBSET", [s])])) in
      ("zenon_in_SUBSET", [tr_term e1; tr_term s], [c], [[h1]])
  | Ext (_, "notin_SUBSET", [e1; s]) ->
      let h1 = tr_prop (enot (eapp ("TLA.subseteq", [e1; s]))) in
      let c = tr_prop (enot (eapp ("TLA.in", [e1; eapp ("TLA.SUBSET", [s])]))) in
      ("zenon_notin_SUBSET", [tr_term e1; tr_term s], [c], [[h1]])
  (* UNION *)
  (* INTER *)
  | Ext (_, "in_cup", [e1; e2; e3]) ->
      let h1 = tr_prop (eapp ("TLA.in", [e1; e2])) in
      let h2 = tr_prop (eapp ("TLA.in", [e1; e3])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.cup", [e2; e3])])) in
      ("zenon_in_cup", [tr_term e1; tr_term e2; tr_term e3], [c], [[h1]; [h2]])
  | Ext (_, "notin_cup", [e1; e2; e3]) ->
      let h1 = tr_prop (enot (eapp ("TLA.in", [e1; e2]))) in
      let h2 = tr_prop (enot (eapp ("TLA.in", [e1; e3]))) in
      let c = tr_prop (enot (eapp ("TLA.in", [e1; eapp ("TLA.cup", [e2; e3])])))
      in
      ("zenon_notin_cup", [tr_term e1; tr_term e2; tr_term e3], [c], [[h1; h2]])
  | Ext (_, "in_cap", [e1; e2; e3]) ->
      let h1 = tr_prop (eapp ("TLA.in", [e1; e2])) in
      let h2 = tr_prop (eapp ("TLA.in", [e1; e3])) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.cap", [e2; e3])])) in
      ("zenon_in_cap", [tr_term e1; tr_term e2; tr_term e3], [c], [[h1; h2]])
  | Ext (_, "notin_cap", [e1; e2; e3]) ->
      let h1 = tr_prop (enot (eapp ("TLA.in", [e1; e2]))) in
      let h2 = tr_prop (enot (eapp ("TLA.in", [e1; e3]))) in
      let c = tr_prop (enot (eapp ("TLA.in", [e1; eapp ("TLA.cap", [e2; e3])])))
      in
      ("zenon_notin_cap", [tr_term e1; tr_term e2; tr_term e3], [c],
       [[h1]; [h2]])
  | Ext (_, "in_setminus", [e1; e2; e3]) ->
      let h1 = tr_prop (eapp ("TLA.in", [e1; e2])) in
      let h2 = tr_prop (enot (eapp ("TLA.in", [e1; e3]))) in
      let c = tr_prop (eapp ("TLA.in", [e1; eapp ("TLA.setminus", [e2; e3])])) in
      ("zenon_in_setminus", [tr_term e1; tr_term e2; tr_term e3], [c],
       [[h1; h2]])
  | Ext (_, "notin_setminus", [e1; e2; e3]) ->
      let h1 = tr_prop (enot (eapp ("TLA.in", [e1; e2]))) in
      let h2 = tr_prop (eapp ("TLA.in", [e1; e3])) in
      let c = tr_prop (enot (eapp ("TLA.in",
                                   [e1; eapp ("TLA.setminus", [e2; e3])])))
      in
      ("zenon_notin_setminus", [tr_term e1; tr_term e2; tr_term e3], [c],
       [[h1]; [h2]])
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
  (* setOfAll *)
  | Ext (_, "in_funcset", [f; a; b]) ->
      let h1 = eapp ("TLA.isAFcn", [f]) in
      let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]) in
      let x = Expr.newvar () in
      let h3 = eall (x, "",
                 eimply (eapp ("TLA.in", [x; a]),
                         eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
      in
      let c = tr_prop (eapp ("TLA.in", [f; eapp ("TLA.FuncSet", [a; b])])) in
      ("zenon_in_funcset", List.map tr_term [f; a; b], [c],
                           [List.map tr_prop [h1; h2; h3]])
  | Ext (_, "notin_funcset", [f; a; b]) ->
      let h1 = eapp ("TLA.isAFcn", [f]) in
      let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]) in
      let x = Expr.newvar () in
      let h3 = eall (x, "",
                 eimply (eapp ("TLA.in", [x; a]),
                         eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
      in
      let c = tr_prop (eapp ("TLA.in", [f; eapp ("TLA.FuncSet", [a; b])])) in
      ("zenon_notin_funcset", List.map tr_term [f; a; b], [c],
       List.map (fun x -> [enot x]) [h1; h2; h3])
  | Ext (_, "setext", [e1; e2]) ->
      let x = Expr.newvar () in
      let h1 = tr_prop (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                             eapp ("TLA.in", [x; e2]))))
      in
      let c = tr_prop (eapp ("=", [e1; e2])) in
      ("zenon_setext", [tr_term e1; tr_term e2], [c], [[h1]])
  | Ext (_, "notsetext", [e1; e2]) ->
      let x = Expr.newvar () in
      let h1 = tr_prop (enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                                   eapp ("TLA.in", [x; e2])))))
      in
      let c = tr_prop (enot (eapp ("=", [e1; e2]))) in
      ("zenon_notsetext", [tr_term e1; tr_term e2], [c], [[h1]])
  | Ext (_, "funext", [e1; e2]) ->
     let x = Expr.newvar () in
     let h1 = tr_prop (eall (x, "", eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                                eapp ("TLA.fapply", [e2; x])])))
     in
     let c = tr_prop (eapp ("=", [e1; e2])) in
     ("zenon_funext", [tr_term e1; tr_term e2], [c], [[h1]])
  | Ext (_, "fapplyfcn",
         [(Elam (cv, _, cb, _) as ctx); s; (Elam (v, _, b, _) as l); a]) ->
     let h1 = tr_prop (enot (eapp ("TLA.in", [a; s]))) in
     let newarg = Expr.substitute [(v, a)] b in
     let h2 = tr_prop (Expr.substitute [(cv, newarg)] cb) in
     let oldarg = eapp ("TLA.fapply", [eapp ("TLA.Fcn", [s; l]); a]) in
     let c = tr_prop (Expr.substitute [(cv, oldarg)] cb) in
     ("zenon_fapplyfcn", [tr_prop ctx; tr_term s; tr_term l; tr_term a],
      [c], [[h1]; [h2]])
  | Ext (_, "fapplyfcn", _) -> assert false
  | Ext (group, name, _) ->
      eprintf "unknown extension: %s_%s\n" group name;
      flush stderr;
      assert false
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

let declare_context_coq oc = [];;

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
