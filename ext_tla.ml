(*  Copyright 2008 INRIA  *)
Version.add "$Id: ext_tla.ml,v 1.23 2009-01-09 16:28:45 doligez Exp $";;

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
  "TLA.set";
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
  "TLA.DOMAIN";
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

let mkbranches hs = Array.of_list (List.map (fun x -> [x]) hs);;

let rec decompose_add e =
  match e with
  | Eapp ("TLA.add", [e1; e2], _) ->
     let (l, rest) = decompose_add e2 in (e1 :: l, rest)
  | _ -> ([], e)
;;

let newnodes_prop e g =
  let mknode prio name args branches =
    [ Node {
      nconc = [e];
      nrule = Ext ("tla", name, args);
      nprio = prio;
      ngoal = g;
      nbranches = branches;
    } ]
  in
  let nometa e =
    match e with
    | Emeta _ | Elam _ -> false
    | _ -> true
  in
  match e with
  | Eapp ("=", [e1; Etrue], _) when nometa e1 ->
     mknode Prop "eq_x_true" [e; e1; e1] [| [e1] |]

  | Eapp ("=", [Etrue; e1], _) when nometa e1 ->
     mknode Prop "eq_true_x" [e; e1; e1] [| [e1] |]

  | Enot (Eapp ("=", [e1; Etrue], _), _) when nometa e1 ->
     let h1 = enot (e1) in
     mknode Prop "noteq_x_true" [e; h1; e1] [| [h1] |]

  | Enot (Eapp ("=", [Etrue; e1], _), _) when nometa e1 ->
     let h1 = enot (e1) in
     mknode Prop "noteq_true_x" [e; h1; e1] [| [h1] |]

  | Eapp ("=", [e1; Efalse], _) when nometa e1 ->
     let h = enot (e1) in
     mknode Prop "eq_x_false" [e; h; e1] [| [h] |]

  | Eapp ("=", [Efalse; e1], _) when nometa e1 ->
     let h = enot (e1) in
     mknode Prop "eq_false_x" [e; h; e1] [| [h] |]

  | Eapp ("TLA.in", [e1; Evar ("TLA.emptyset", _)], _) ->
    mknode Prop "in_emptyset" [e; e1] [| |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _) ->
    let h1 = eapp ("=", [e1; e2]) in
    let h2 = eapp ("=", [e1; e3]) in
    mknode Prop "in_upair" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.upair", [e2; e3], _)], _), _) ->
    let h1 = enot (eapp ("=", [e1; e2])) in
    let h2 = enot (eapp ("=", [e1; e3])) in
    mknode Prop "notin_upair" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.add", [e2; e3], _) as s], _) ->
     let (elems, rest) = decompose_add s in
     let helems = List.map (fun x -> eapp ("=", [e1; x])) elems in
     let hs =
       if Expr.equal rest (evar "TLA.emptyset") then helems
       else helems @ [eapp ("TLA.in", [e1; rest])]
     in
     mknode Prop "in_add" [e; e1; s] (mkbranches hs)
  | Eapp ("TLA.in", [e1; Eapp ("TLA.set", elems, _) as s], _) ->
     let helems = List.map (fun x -> eapp ("=", [e1; x])) elems in
     mknode Prop "in_set" [e; e1; s] (mkbranches helems)
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.add", [e2; e3], _) as s], _), _) ->
     let (elems, rest) = decompose_add s in
     let helems = List.map (fun x -> enot (eapp ("=", [e1; x]))) elems in
     let hs =
       if Expr.equal rest (evar "TLA.emptyset") then helems
       else enot (eapp ("TLA.in", [e1; rest])) :: helems
     in
     mknode Prop "notin_add" [e; e1; s] [| hs |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.set", elems, _) as s], _), _) ->
     let helems = List.map (fun x -> enot (eapp ("=", [e1; x]))) elems in
     mknode Prop "notin_set" [e; e1; s] [| helems |]

  (* infinity -- needed ? *)

  | Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _) ->
     let h1 = eapp ("TLA.subseteq", [e1; s]) in
     mknode Prop "in_SUBSET" [e; h1; e1; s] [| [h1] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.SUBSET", [s], _)], _), _) ->
     let h1 = enot (eapp ("TLA.subseteq", [e1; s])) in
     mknode Prop "notin_SUBSET" [e; h1; e1; s] [| [h1] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.UNION", [s], _)], _) ->
     let b = Expr.newvar () in
     let h1 = eex (b, "", eand (eapp ("TLA.in", [b; s]),
                                eapp ("TLA.in", [e1; b]))) in
     mknode Prop "in_UNION" [e; h1; e1; s] [| [h1] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.UNION", [s], _)], _), _) ->
     let b = Expr.newvar () in
     let h1 = enot (eex (b, "", eand (eapp ("TLA.in", [b; s]),
                                      eapp ("TLA.in", [e1; b])))) in
     mknode Arity "notin_UNION" [e; h1; e1; s] [| [h1] |]

  (* INTER -- needed ? *)

  | Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "in_cup" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cup", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "notin_cup" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "in_cap" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.cap", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "notin_cap" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]

  | Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _) ->
     let h1 = eapp ("TLA.in", [e1; e2]) in
     let h2 = enot (eapp ("TLA.in", [e1; e3])) in
     mknode Prop "in_setminus" [e; h1; h2; e1; e2; e3] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in", [e1; Eapp ("TLA.setminus", [e2; e3], _)], _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; e2])) in
     let h2 = eapp ("TLA.in", [e1; e3]) in
     mknode Prop "notin_setminus" [e; h1; h2; e1; e2; e3] [| [h1]; [h2] |]

  | Eapp ("TLA.in",
          [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
          _) ->
     let h1 = eapp ("TLA.in", [e1; s]) in
     let h2 = substitute [(v, e1)] p in
     mknode Prop "in_subsetof" [e; h1; h2; e1; s; pred] [| [h1; h2] |]
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.subsetOf", [s; Elam (v, _, p, _) as pred], _)],
                _), _) ->
     let h1 = enot (eapp ("TLA.in", [e1; s])) in
     let h2 = enot (substitute [(v, e1)] p) in
     mknode Prop "notin_subsetof" [e; h1; h2; e1; s; pred] [| [h1]; [h2] |]

  | Eapp ("TLA.in",
          [e1; Eapp ("TLA.setOfAll", [s; Elam (v, _, p, _) as pred], _)],
          _) ->
     let x = Expr.newvar () in
     let h1 = eex (x, "", eand (eapp ("TLA.in", [x; s]),
                                eapp ("=", [e1; substitute [(v, x)] p])))
     in
     mknode (Inst h1) "in_setofall" [e; h1; e1; s; pred] [| [h1] |]
  | Enot (Eapp ("TLA.in",
                [e1; Eapp ("TLA.setOfAll", [s; Elam (v, _, p, _) as pred], _)],
                _), _) ->
     let x = Expr.newvar () in
     let h1 = enot (eex (x, "", eand (eapp ("TLA.in", [x; s]),
                                      eapp ("=", [e1; substitute [(v, x)] p]))))
     in
     mknode (Inst h1) "notin_setofall" [e; h1; e1; s; pred] [| [h1] |]

  | Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _) ->
     let h1 = eapp ("TLA.isAFcn", [f]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]) in
     let x = Expr.newvar () in
     let h3 = eall (x, "",
                eimply (eapp ("TLA.in", [x; a]),
                        eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b])))
     in
     mknode (Inst h3) "in_funcset" [e; h1; h2; h3; f; a; b] [| [h1; h2; h3] |]
  | Enot (Eapp ("TLA.in", [f; Eapp ("TLA.FuncSet", [a; b], _)], _), _) ->
     let h1 = enot (eapp ("TLA.isAFcn", [f])) in
     let h2 = enot (eapp ("=", [eapp ("TLA.DOMAIN", [f]); a]))
     in
     let x = Expr.newvar () in
     let h3 = enot (
               eall (x, "",
                     eimply (eapp ("TLA.in", [x; a]),
                             eapp ("TLA.in", [eapp ("TLA.fapply", [f; x]); b]))))
     in
     mknode (Inst h3) "notin_funcset" [e; h1; h2; h3; f; a; b]
            [| [h1]; [h2]; [h3] |]

  | Eapp ("=", [e1; e2], _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let h = eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                  eapp ("TLA.in", [x; e2])))
     in
     mknode (Inst h) "setequal" [e; h; e1; e2] [| [h] |]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_set_expr e1 || is_set_expr e2 ->
     let x = Expr.newvar () in
     let h = enot (eall (x, "", eequiv (eapp ("TLA.in", [x; e1]),
                                        eapp ("TLA.in", [x; e2]))))
     in
     mknode (Inst h) "notsetequal" [e; h; e1; e2] [| [h] |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.Fcn", [s; l], _)], _), _) ->
     mknode Prop "notisafcn_fcn" [e; s; l] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.except", [f; v; e1], _)], _), _) ->
     mknode Prop "notisafcn_except" [e; f; v; e1] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.oneArg", [e1; e2], _)], _), _) ->
     mknode Prop "notisafcn_onearg" [e; e1; e2] [| |]

  | Enot (Eapp ("TLA.isAFcn", [Eapp ("TLA.extend", [f; g], _)], _), _) ->
     mknode Prop "notisafcn_extend" [e; f; g] [| |]

  | Eapp ("=", [e1; e2], _) when is_fcn_expr e1 || is_fcn_expr e2 ->
     let x = Expr.newvar () in
     let h1 = eequiv (eapp ("TLA.isAFcn", [e1]), eapp ("TLA.isAFcn", [e2])) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [e1]); eapp ("TLA.DOMAIN", [e2])])
     in
     let h3 = eall (x, "", eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                       eapp ("TLA.fapply", [e2; x])]))
     in
     let h = eand (eand (h1, h2), h3) in
     mknode (Inst h3) "funequal" [e; h; e1; e2] [| [h] |]
  | Enot (Eapp ("=", [e1; e2], _), _) when is_fcn_expr e1 || is_fcn_expr e2 ->
     let x = Expr.newvar () in
     let h0 = eapp ("TLA.isAFcn", [e1]) in
     let h1 = eapp ("TLA.isAFcn", [e2]) in
     let h2 = eapp ("=", [eapp ("TLA.DOMAIN", [e1]); eapp ("TLA.DOMAIN", [e2])])
     in
     let h3 = eall (x, "", eimply (eapp ("TLA.in", [x; eapp("TLA.DOMAIN",[e2])]),
                                   eapp ("=", [eapp ("TLA.fapply", [e1; x]);
                                               eapp ("TLA.fapply", [e2; x])])))
     in
     let h = enot (eand (eand (eand (h0, h1), h2), h3)) in
     mknode (Inst h3) "notfunequal" [e; h; e1; e2] [| [h] |]
  | _ -> []
;;

let apply f e =
  match f with
  | Elam (v, _, b, _) -> Expr.substitute [(v, e)] b
  | _ -> assert false
;;

let rec rewrites in_expr ctx e mknode =
  let lamctx = let x = Expr.newvar () in elam (x, "", ctx x) in
  let mk_boolcase name e1 e2 =
    let h1a = eapp ("=", [e; etrue]) in
    let h1b = ctx (etrue) in
    let h2a = eapp ("=", [e; efalse]) in
    let h2b = ctx (efalse) in
    mknode ("boolcase_" ^ name) [ctx e; h1a; h1b; h2a; h2b; lamctx; e1; e2]
           [] [| [h1a; h1b]; [h2a; h2b] |]
  in
  match e with
  | _ when in_expr && Index.member e ->
     let h1 = ctx (etrue) in
     mknode "trueistrue" [ctx e; e; h1; lamctx; e] [e] [| [h1] |]
  | Evar (f, _) when in_expr && Index.has_def f ->
     let (d, params, body) = Index.get_def f in
     if params = [] then begin
       let unfolded = ctx body in
       mknode "definition" [ctx e; unfolded; e] [] [| [unfolded] |]
     end else
       []
  | Eapp (f, args, _) when in_expr && Index.has_def f ->
     let (d, params, body) = Index.get_def f in
     if List.length params = List.length args then begin
       let s = List.combine params args in
       let unfolded = ctx (substitute s body) in
       mknode "definition" [ctx e; unfolded; e] [] [| [unfolded] |]
     end else
       []
  | Eapp ("TLA.fapply", [Eapp ("TLA.Fcn", [s; Elam (v, _, b, _) as l], _); a], _)
  -> let h1 = enot (eapp ("TLA.in", [a; s])) in
     let h2 = ctx (Expr.substitute [(v, a)] b) in
     mknode "fapplyfcn" [ctx e; h1; h2; lamctx; s; l; a] [] [| [h1]; [h2] |]
  | Eapp ("TLA.fapply", [Eapp ("TLA.except", [f; v; e1], _); w], _) ->
     let indom = eapp ("TLA.in", [w; eapp ("TLA.DOMAIN", [f])]) in
     let h1a = indom in
     let h1b = eapp ("=", [v; w]) in
     let h1c = ctx e1 in
     let h2a = indom in
     let h2b = enot (eapp ("=", [v; w])) in
     let h2c = ctx (eapp ("TLA.fapply", [f; w])) in
     let h3 = enot indom in
     mknode "fapplyexcept" [ctx e; h1a; h1b; h1c; h2a; h2b; h2c; h3;
                            lamctx; f; v; e1; w]
            [] [| [h1a; h1b; h1c]; [h2a; h2b; h2c]; [h3] |]
  | Eapp ("TLA.fapply", [f; a], _) ->
     rewrites true (fun x -> ctx (eapp ("TLA.fapply", [x; a]))) f mknode
     @ rewrites true (fun x -> ctx (eapp ("TLA.fapply", [f; x]))) a mknode
  | Eapp ("TLA.DOMAIN", [Eapp ("TLA.except", [f; v; e1], _)], _) ->
     let h1 = ctx (eapp ("TLA.DOMAIN", [f])) in
     mknode "domain_except" [ctx e; h1; lamctx; f; v; e1] [] [| [h1] |]
  | Eapp ("TLA.DOMAIN", [Eapp ("TLA.Fcn", [s; l], _)], _) ->
     let h1 = ctx (s) in
     mknode "domain_fcn" [ctx e; h1; lamctx; s; l] [] [| [h1] |]
  | Eapp ("TLA.DOMAIN", [f], _) ->
     rewrites true (fun x -> ctx (eapp ("TLA.DOMAIN", [x]))) f mknode
  | Enot (e1, _) when in_expr ->
     let h1a = eapp ("=", [e; etrue]) in
     let h1b = ctx (etrue) in
     let h2a = eapp ("=", [e; efalse]) in
     let h2b = ctx (efalse) in
     mknode ("boolcase_not") [ctx e; h1a; h1b; h2a; h2b; lamctx; e1]
            [] [| [h1a; h1b]; [h2a; h2b] |]
  | Eand (e1, e2, _) when in_expr -> mk_boolcase "and" e1 e2
  | Eor (e1, e2, _) when in_expr -> mk_boolcase "or" e1 e2
  | Eimply (e1, e2, _) when in_expr -> mk_boolcase "imply" e1 e2
  | Eequiv (e1, e2, _) when in_expr -> mk_boolcase "equiv" e1 e2
  | Eapp ("=", [e1; e2], _) when in_expr -> mk_boolcase "equal" e1 e2
  (* FIXME missing : Eall, Eex *)

  | Eapp ("TLA.cond", [Etrue; e1; e2], _) ->
     let h1 = ctx (e1) in
     mknode "iftrue" [ctx e; h1; lamctx; e1; e2] [] [| [h1] |]
  | Eapp ("TLA.cond", [Efalse; e1; e2], _) ->
     let h1 = ctx (e2) in
     mknode "iffalse" [ctx e; h1; lamctx; e1; e2] [] [| [h1] |]
  | Eapp ("TLA.cond", [e0; e1; e2], _) ->
     let h1a = e0 in
     let h1b = ctx (e1) in
     let h2a = enot (e0) in
     let h2b = ctx (e2) in
     mknode "ifthenelse" [ctx e; h1a; h1b; h2a; h2b; lamctx; e0; e1; e2] []
            [| [h1a; h1b]; [h2a; h2b] |]
  | _ -> []
;;

let rec find_rewrites in_expr ctx e mknode =
  let local = rewrites in_expr ctx e mknode in
  match e with
  | _ when local <> [] -> local
  | Eapp (p, args, _) ->
     let rec loop leftarg rightarg =
       match rightarg with
       | [] -> []
       | h::t ->
          let newctx x = ctx (eapp (p, List.rev_append leftarg (x :: t)))
          in
          begin match find_rewrites true newctx h mknode with
          | [] -> loop (h::leftarg) t
          | l -> l
          end
     in
     loop [] args
  | Enot (e1, _) -> find_rewrites false (fun x -> (ctx (enot x))) e1 mknode
  | _ -> []
;;

let newnodes_rewrites e g =
  let mknode name args add_con branches =
    match name with
    | "definition" ->
       begin match args with
       | [folded; unfolded; Evar (f, _)] ->
          let (def, params, body) = Index.get_def f in
          [ Node {
            nconc = e :: add_con;
            nrule = Definition (def, folded, unfolded);
            nprio = Arity;
            ngoal = g;
            nbranches = branches;
          }]
       | [folded; unfolded; Eapp (f, args, _)] ->
          let (def, params, body) = Index.get_def f in
          [ Node {
            nconc = e :: add_con;
            nrule = Definition (def, folded, unfolded);
            nprio = Arity;
            ngoal = g;
            nbranches = branches;
          }]
       | _ -> assert false
       end
    | _ ->
       [ Node {
         nconc = e :: add_con;
         nrule = Ext ("tla", name, args);
         nprio = Arity;
         ngoal = g;
         nbranches = branches;
       }]
  in
  find_rewrites false (fun x -> x) e mknode
;;

let newnodes e g =
  newnodes_prop e g @ newnodes_rewrites e g
;;

let to_llargs r =
  let alpha r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1; h2] ])
    | _ -> assert false
  in
  let beta r =
    match r with
    | Ext (_, name, c :: h1 :: h2 :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1]; [h2] ])
    | _ -> assert false
  in
  let beta2 r =
    match r with
    | Ext (_, name, c :: h1a :: h1b :: h2a :: h2b :: args) ->
       ("zenon_" ^ name, args, [c], [ [h1a; h1b]; [h2a; h2b] ])
    | _ -> assert false
  in
  let single r =
    match r with
    | Ext (_, name, c :: h :: args) -> ("zenon_" ^ name, args, [c], [ [h] ])
    | _ -> assert false
  in
  let close r =
    match r with
    | Ext (_, name, c :: args) -> ("zenon_" ^ name, args, [c], [])
    | _ -> assert false
  in
  match r with
  | Ext (_, "in_emptyset", [c; e1]) -> ("zenon_in_emptyset", [e1], [c], [])
  | Ext (_, "in_upair", _) -> beta r
  | Ext (_, "notin_upair", _) -> alpha r
  | Ext (_, "in_cup", _) -> beta r
  | Ext (_, "notin_cup", _) -> alpha r
  | Ext (_, "in_cap", _) -> alpha r
  | Ext (_, "notin_cap", _) -> beta r
  | Ext (_, "in_setminus", _) -> alpha r
  | Ext (_, "notin_setminus", _) -> beta r
  | Ext (_, "in_subsetof", _) -> alpha r
  | Ext (_, "notin_subsetof", _) -> beta r
  | Ext (_, "in_funcset", [c; h1; h2; h3; f; a; b]) ->
     ("zenon_in_funcset", [f; a; b], [c], [ [h1; h2; h3] ])
  | Ext (_, "notin_funcset", [c; h1; h2; h3; f; a; b]) ->
     ("zenon_notin_funcset", [f; a; b], [c], [ [h1]; [h2]; [h3] ])
  | Ext (_, "trueistrue", [c1; c2; h1; ctx; e1]) ->
     ("zenon_trueistrue", [ctx; e1], [c1; c2], [ [h1] ])
  | Ext (_, "fapplyfcn", _) -> beta r
  | Ext (_, "fapplyexcept", [c; h1a; h1b; h1c; h2a; h2b; h2c; h3;
                             ctx; f; v; e1; w]) ->
     ("zenon_fapplyexcept", [ctx; f; v; e1; w], [c],
      [ [h1a; h1b; h1c]; [h2a; h2b; h2c]; [h3] ])
  | Ext (_, "boolcase_not", _) -> beta2 r
  | Ext (_, "boolcase_and", _) -> beta2 r
  | Ext (_, "boolcase_or", _) -> beta2 r
  | Ext (_, "boolcase_imply", _) -> beta2 r
  | Ext (_, "boolcase_equiv", _) -> beta2 r
  | Ext (_, "notisafcn_fcn", _) -> close r
  | Ext (_, "notisafcn_except", _) -> close r
  | Ext (_, "notisafcn_onearg", _) -> close r
  | Ext (_, "notisafcn_extend", _) -> close r
  | Ext (_, "ifthenelse", _) -> beta2 r
  | Ext (_, name, _) -> single r
  | _ -> assert false
;;

let is_simple r =
  match r with
  | Ext (_, "in_add", _) -> false
  | Ext (_, "notin_add", _) -> false
  | _ -> true
;;

let to_llproof tr_expr mlp args =
  match mlp.mlrule with
  | Ext (_, "in_add", [c; x; s]) ->
     let subexts = Array.to_list args in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s subexts myconc =
       match s, subexts with
       | Evar ("TLA.emptyset", _), _ ->
         let tconc = tre (eapp ("TLA.in", [x; s])) in
         let n0 = {
           Llproof.conc = trl myconc;
           Llproof.rule = Llproof.Rextension ("zenon_in_emptyset",
                                              [tre x], [tconc], []);
           Llproof.hyps = [];
         } in
         (n0, [])
       | Eapp ("TLA.add", [y; s1], _), ((sub, ext) :: t) ->
          let concl = eapp ("TLA.in", [x; s]) in
          let h1 = eapp ("=", [x; y]) in
          let h2 = eapp ("TLA.in", [x; s1]) in
          let (sub1, ext1) = mkproof s1 t (h2 :: myconc) in
          let extras = Expr.diff (Expr.union ext ext1) myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("zenon_in_add",
                                               trl [x; y; s1], [tre concl],
                                               [ [tre h1]; [tre h2] ]);
            Llproof.hyps = [sub; sub1];
          } in
          (n0, extras)
        | _, [subext] -> subext
        | _ -> assert false
     in
     mkproof s subexts mlp.mlconc
  | Ext (_, "in_set", [c; x; s]) ->
     let subexts = Array.to_list args in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s subexts myconc =
       match s, subexts with
       | Eapp ("TLA.set", [], _), [] ->
         let tconc = tre (eapp ("TLA.in", [x; s])) in
         let n0 = {
           Llproof.conc = trl myconc;
           Llproof.rule = Llproof.Rextension ("zenon_in_emptyset",
                                              [tre x], [tconc], []);
           Llproof.hyps = [];
         } in
         (n0, [])
       | Eapp ("TLA.set", y :: l1, _), ((sub, ext) :: t) ->
          let s1 = eapp ("TLA.set", l1) in
          let concl = eapp ("TLA.in", [x; s]) in
          let h1 = eapp ("=", [x; y]) in
          let h2 = eapp ("TLA.in", [x; s1]) in
          let (sub1, ext1) = mkproof s1 t (h2 :: myconc) in
          let extras = Expr.diff (Expr.union ext ext1) myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("zenon_in_add",
                                               trl [x; y; s1], [tre concl],
                                               [ [tre h1]; [tre h2] ]);
            Llproof.hyps = [sub; sub1];
          } in
          (n0, extras)
        | _ -> assert false
     in
     mkproof s subexts mlp.mlconc
  | Ext (_, "notin_add", [c; x; s]) ->
     let (sub, ext) =
       match args with
       | [| (sub, ext) |] -> (sub, ext)
       | _ -> assert false
     in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s myconc =
       match s with
       | Eapp ("TLA.add", [y; s1], _) ->
          let concl = enot (eapp ("TLA.in", [x; s])) in
          let h1 = enot (eapp ("=", [x; y])) in
          let h2 = enot (eapp ("TLA.in", [x; s1])) in
          let (sub1, ext1) = mkproof s1 (h1 :: h2 :: myconc) in
          let extras = Expr.diff ext1 myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("zenon_notin_add",
                                               trl [x; y; s1], [tre concl],
                                               [ trl [h1; h2] ]);
            Llproof.hyps = [sub1];
          } in
          (n0, extras)
       | _ -> (sub, ext)
     in
     mkproof s mlp.mlconc
  | Ext (_, "notin_set", [c; x; s]) ->
     let (sub, ext) =
       match args with
       | [| (sub, ext) |] -> (sub, ext)
       | _ -> assert false
     in
     let tre = tr_expr in
     let trl l = List.map tr_expr l in
     let rec mkproof s myconc =
       match s with
       | Eapp ("TLA.set", y :: l1, _) ->
          let s1 = eapp ("TLA.set", l1) in
          let concl = enot (eapp ("TLA.in", [x; s])) in
          let h1 = enot (eapp ("=", [x; y])) in
          let h2 = enot (eapp ("TLA.in", [x; s1])) in
          let (sub1, ext1) = mkproof s1 (h1 :: h2 :: myconc) in
          let extras = Expr.diff ext1 myconc in
          let n0 = {
            Llproof.conc = trl (extras @@ myconc);
            Llproof.rule = Llproof.Rextension ("zenon_notin_add",
                                               trl [x; y; s1], [tre concl],
                                               [ trl [h1; h2] ]);
            Llproof.hyps = [sub1];
          } in
          (n0, extras)
       | _ -> (sub, ext)
     in
     mkproof s mlp.mlconc
  | _ ->
     let (name, meta, con, hyps) = to_llargs mlp.mlrule in
     let tmeta = List.map tr_expr meta in
     let tcon = List.map tr_expr con in
     let thyps = List.map (List.map tr_expr) hyps in
     let (subs, exts) = List.split (Array.to_list args) in
     let ext = List.fold_left Expr.union [] exts in
     let extras = Expr.diff ext mlp.mlconc in
     let nn = {
         Llproof.conc = List.map tr_expr (extras @@ mlp.mlconc);
         Llproof.rule = Llproof.Rextension (name, tmeta, tcon, thyps);
         Llproof.hyps = subs;
       }
     in (nn, extras)
;;

let preprocess l = l;;

let add_phrase p = ();;

let postprocess p = p;;

let declare_context_coq oc = [];;

Extension.register {
  Extension.name = "tla";
  Extension.newnodes = newnodes;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = preprocess;
  Extension.add_phrase = add_phrase;
  Extension.postprocess = postprocess;
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
};;
