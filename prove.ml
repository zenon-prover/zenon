(*  Copyright 2002 INRIA  *)
Version.add "$Id: prove.ml,v 1.7 2004-06-04 09:29:15 doligez Exp $";;

open Printf;;

open Expr;;
open Mlproof;;
open Node;;
open Prio;;

type branch_state =
  | Open
  | Closed of proof
  | Back of expr list
;;

type snode = {
  sconc : expr list;
  srule : rule;
  sprio : Prio.t;
  ssize : int;
  sbranches : expr list array;
};;

type frame = {
  node : snode;
  queue : snode Heap.t;
  state : branch_state array;
  cur : int;
};;

(***************)


let origin_ponderation = 10000;;
let size_ponderation = 13;;
let weight_ponderation = 10;;

(***************)

let (@@) = List.rev_append;;

(***************)

let cur_depth = ref 0;;
let top_depth = ref 0;;

(****************)

let complement fm =
  match fm with
  | Enot (p, _) -> (p, p)
  | p -> (enot (p), p)
;;

let rec replace_meta m va e =
  match e with
  | Evar _ -> e
  | Emeta _ -> if Expr.equal e m then va else e
  | Eapp (s, args, _) -> eapp (s, List.map (replace_meta m va) args)
  | Enot (f, _) -> enot (replace_meta m va f)
  | Eand (f, g, _) -> eand (replace_meta m va f, replace_meta m va g)
  | Eor (f, g, _) -> eor (replace_meta m va f, replace_meta m va g)
  | Eimply (f, g, _) -> eimply (replace_meta m va f, replace_meta m va g)
  | Eequiv (f, g, _) -> eequiv (replace_meta m va f, replace_meta m va g)
  | Etrue -> e
  | Efalse -> e
  | Eall (v, t, f, _) -> eall (v, t, replace_meta m va f)
  | Eex (v, t, f, _) -> eex (v, t, replace_meta m va f)
  | Etau (v, t, f, _) -> etau (v, t, replace_meta m va f)
;;

(****************)

let list_max accu l =
  List.fold_left (fun a e -> max a (Expr.size e)) accu l
;;

let add_size n = {
  sconc = n.nconc;
  srule = n.nrule;
  sprio = n.nprio;
  sbranches = n.branches;
  ssize = Array.fold_left list_max 0 n.branches;
};;

(****************)

(* [make_inst m e prio extra_weight]
   create the node that instantiates m with e,
   give it a priority relative to [prio] + [extra_weight]
*)
let make_inst m e prio extra_weight =
  let mm = emeta m in
  if Expr.occurs mm e then begin
    match m with
    | Eall (v, t, p, _) ->
        let f = replace_meta mm (evar v) e in
        let n = eall (v, t, Expr.substitute [(v, f)] p) in
        {
          nconc = [m];
          nrule = AllPartial (m, n);
          nprio = Prio.update prio sh_all_partial (weight_part + extra_weight)
                              (Index.get_meta m);
          branches = [| [n] |];
        }
    | Enot (Eex (v, t, p, _), _) ->
        let f = replace_meta mm (evar v) e in
        let n = enot (eex (v, t, Expr.substitute [(v, f)] p)) in
        {
          nconc = [m];
          nrule = NotExPartial (m, n);
          nprio = Prio.update prio sh_notex_partial (weight_part + extra_weight)
                              (Index.get_meta m);
          branches = [| [n] |];
        }
    | _ -> assert false
  end else begin
    match m with
    | Eall (v, t, p, _) -> {
          nconc = [m];
          nrule = All (m, e);
          nprio = Prio.update prio sh_all_inst (weight_inst + extra_weight)
                              (Index.get_meta m);
          branches = [| [Expr.substitute [(v, e)] p] |];
        }
    | Enot (Eex (v, t, p, _), _) -> {
          nconc = [m];
          nrule = NotEx (m, e);
          nprio = Prio.update prio sh_notex_inst (weight_inst + extra_weight)
                              (Index.get_meta m);
          branches = [| [enot (Expr.substitute [(v, e)] p)] |];
        }
    | _ -> assert false
  end
;;

(* [make_inequals l1 l2]
   l1 and l2 are the same length
   returns the pairwise inequalities between corresponding elements of l1 and l2
   return it as an array of lists
*)
let rec make_inequals_aux l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | h1::t1, h2::t2 ->
      [enot (eapp ("=", [h1; h2]))] :: make_inequals_aux t1 t2
  | _, _ -> assert false
;;
let make_inequals l1 l2 = Array.of_list (make_inequals_aux l1 l2);;

let make_eq_noteq_node prio1 prio2 e1 e2 f1 f2 =
  let w1 = if (has_meta e1 || has_meta e2) && (has_meta f1 || has_meta f2)
           then weight_meta_neq
           else 0
  in
  {
    nconc = [eapp ("=", [e1; e2]); enot (eapp ("=", [f1; f2]))];
    nrule = Equal_NotEqual (e1, e2, f1, f2);
    nprio = {
      Prio.shape = sh_equal_notequal;
      Prio.origin = min prio1.Prio.origin prio2.Prio.origin;
      Prio.weight1 = prio1.Prio.weight1 + weight_equal_notequal + w1;
      Prio.weight2 = prio2.Prio.weight1;
    };
    branches = [| [enot (eapp ("=", [f1; e1])); enot (eapp ("=", [f1; e2]))];
                  [enot (eapp ("=", [e1; f2])); enot (eapp ("=", [e2; f2]))] |];
  }
;;

(* [correlate_equal eq prio]
   make the nodes corresponding to all combinations of [eq] with
   the inequations present in the branch that match a member of [eq]
*)
let correlate_equal eq prio =
  let (e1, e2) = match eq with
     | Eapp ("=", [e1; e2], _) -> (e1, e2)
     | _ -> assert false
  in
  let good e neq =
    match neq with
    | Enot (Eapp ("=", [Emeta _; _], _), _) -> assert false
    | Enot (Eapp ("=", [_; Emeta _], _), _) -> assert false
    | Enot (Eapp ("=", [f1; f2], _), _) ->
        Expr.preunifiable e f1 || Expr.preunifiable e f2
    | _ -> assert false
  in
  let neqs = List.filter (good e1) (Index.find_noteq e1)
             @@ List.filter (good e2) (Index.find_noteq e2)
  in
  let make_node neq =
    match neq with
    | Enot (Eapp ("=", [f1; f2], _), _) ->
        make_eq_noteq_node prio (Index.get_prio neq) e1 e2 f1 f2
    | _ -> assert false
  in
  List.map make_node neqs
;;

(* [rewrite prio e1 e2 m e]
   m is a metavariable, e is an expression,
   (e1, e2) is (m, e) or (e, m)
   (a) correlate e1 = e2 with the inequalities
   (b) compute critical pairs of e -> m with other oriented equations
   return all the nodes created by (a) and (b)
*)
let rewrite prio e1 e2 e m =
  let good = function
  | Enot (Eapp ("=", [Emeta _; _], _), _) -> assert false
  | Enot (Eapp ("=", [_; Emeta _], _), _) -> assert false
  | Enot (Eapp ("=", [f1; f2], _), _) ->
      Expr.preunifiable e f1 || Expr.preunifiable e f2
  | _ -> assert false
  in
  let neqs = List.filter good (Index.find_noteq e) in
  let make_node neq =
    match neq with
    | Enot (Eapp ("=", [f1; f2], _), _) ->
        make_eq_noteq_node prio (Index.get_prio neq) e1 e2 f1 f2
    | _ -> assert false
  in
  let correl = List.map make_node neqs in
  let good (f, n) =
    not (Expr.equal e f && Expr.equal m n)
    && Expr.preunifiable e f
  in
  let eqs = List.filter good (Index.find_rewrite e) in
  let preunif = List.flatten (List.map (fun (f, n) -> Expr.preunify e f) eqs) in
  let mkinst = function
    | (Emeta (f, _), e) -> make_inst f e prio weight_critpair
    | _ -> assert false
  in
  let insts = List.map mkinst preunif in
  insts @@ correl
;;

(* [correlate_noteq neq prio]
   make the nodes corresponding to all combinations of [neq] with
   the equalities present in the branch that match a member of [neq]
*)
let correlate_noteq neq prio =
  let (e1, e2) = match neq with
    | Enot (Eapp ("=", [e1; e2], _), _) -> (e1, e2)
    | _ -> assert false
  in
  let good e eq =
    match eq with
    | Eapp ("=", [f1; f2], _) ->
        Expr.preunifiable e f1 || Expr.preunifiable e f2
    | _ -> assert false
  in
  let eqs = List.filter (good e1) (Index.find_equal e1)
            @@ List.filter (good e2) (Index.find_equal e2)
  in
  let make_node eq =
    match eq with
    | Eapp ("=", [f1; f2], _) ->
        make_eq_noteq_node prio (Index.get_prio eq) f1 f2 e1 e2
    | _ -> assert false
  in
  List.map make_node eqs
;;

let make_notequiv p np prio1 prio2 =
  match p, np with
  | Eapp (s1, args1, _), Enot (Eapp (s2, args2, _), _) ->
      let w1 = if has_meta p && has_meta np then weight_meta_neq else 0 in
      assert (s1 = s2);
      {
        nconc = [p; np];
        nrule = P_NotP (p, np);
        nprio = {
          Prio.shape = sh_p_notp;
          Prio.origin = min prio1.Prio.origin prio2.Prio.origin;
          Prio.weight1 = prio2.Prio.weight1 + weight_notequiv + w1;
          Prio.weight2 = prio1.Prio.weight1
        };
        branches = make_inequals args1 args2;
      }
  | _ -> assert false
;;

(* [is_conj f m]:
   f is a n-ary conjunctive formula
   return 0 if n >= m; return m-n otherwise
*)
let rec is_conj f m =
  if m <= 0 then 0 else
  match f with
  | Eand (a, b, _) -> is_conj b (is_conj a m)
  | Enot (a, _) -> is_disj a m
  | _ -> m-1

and is_disj f m =
  if m <= 0 then 0 else
  match f with
  | Eor (a, b, _) -> is_disj b (is_disj a m)
  | Eimply (a, b, _) -> is_disj b (is_conj a m)
  | Enot (a, _) -> is_conj a m
  | _ -> m-1
;;

let rec decomp_conj neg accu f =
  match f with
  | Eand (a, b, _) -> decomp_conj neg (decomp_conj neg accu b) a
  | Enot (a, _) -> decomp_disj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu

and decomp_disj neg accu f =
  match f with
  | Eor (a, b, _) -> decomp_disj neg (decomp_disj neg accu b) a
  | Eimply (a, b, _) -> decomp_conj (not neg) (decomp_disj neg accu b) a
  | Enot (a, _) -> decomp_conj (not neg) accu a
  | _ when neg -> enot (f) :: accu
  | _ -> f :: accu
;;

let wrong_arity s =
  if !Globals.warnings_flag then begin
    eprintf "Warning: defined symbol %s is used with wrong arity\n" s;
    flush stderr;
  end;
  []
;;

let add_nodes q (fm, prio) =
  let (nfm, p) = complement fm in
  if Index.member nfm then begin
    Heap.insert q {
      sconc = [fm; nfm];
      srule = Close2 (p);
      sprio = Prio.update prio sh_close2 0 0;
      sbranches = [| |];
      ssize = 0;
    }
  end else
  let (thnodes, thcomplete) = Extension.newnodes fm prio in
  let newnodes =
    if thcomplete then [] else
    match fm with

    (* closure *)
    | Efalse -> [ {
        nconc = [fm];
        nrule = False;
        nprio = Prio.update prio sh_false 0 0;
        branches = [| |];
      } ]
    | Enot (Etrue, _) -> [ {
        nconc = [fm];
        nrule = NotTrue;
        nprio = Prio.update prio sh_false 0 0;
        branches = [| |];
      } ]
    | Enot (Eapp ("=", [a; b], _), _) when Expr.equal a b -> [ {
        nconc = [fm];
        nrule = Close1 (a);
        nprio = Prio.update prio sh_close1 0 0;
        branches = [| |];
      } ]

    | Eapp ("=", [e1; e2], _)
      when Index.member (enot (eapp ("=", [e2; e1]))) -> [ {
        nconc = [fm; (enot (eapp ("=", [e2; e1])))];
        nrule = CloseEq (e1, e2);
        nprio = Prio.update prio sh_closeeq 0 0;
        branches = [| |];
      } ]
    | Enot (Eapp ("=", [e1; e2], _), _)
      when Index.member (eapp ("=", [e2; e1])) -> [ {
        nconc = [fm; (eapp ("=", [e2; e1]))];
        nrule = CloseEq (e2, e1);
        nprio = Prio.update prio sh_closeeq 0 0;
        branches = [| |];
      } ]

    (* special cases for n-ary conjunction and disjunction *)

(* FIXME pourquoi est-ce que test16 et test20 explosent si on fait ca ???
    | Eand _ | Enot (Eor _, _) | Enot (Eimply _, _)
      when is_conj fm 3 = 0 ->
        let forms = decomp_conj false [] fm in
        [ {
          nconc = [fm];
          nrule = ConjTree fm;
          nprio = Prio.update prio sh_and (weight_alpha * List.length forms) 0;
          branches = [| forms |];
        } ]
*)
    | Eor _ | Enot (Eand _, _) | Eimply _
      when is_disj fm 3 = 0 ->
        let forms = Array.of_list (decomp_disj false [] fm) in
        [ {
          nconc = [fm];
          nrule = DisjTree fm;
          nprio = Prio.update prio sh_or (weight_beta * Array.length forms) 0;
          branches = Array.map (fun x -> [x]) forms;
        } ]

    (* alpha *)
    | Enot (Enot (a, _), _) -> [ {
        nconc = [fm];
        nrule = NotNot (a);
        nprio = Prio.update prio sh_notnot weight_alpha 0;
        branches = [| [ a ] |];
      } ]
    | Eand (a, b, _) -> [ {
        nconc = [fm];
        nrule = And (a, b);
        nprio = Prio.update prio sh_and weight_alpha 0;
        branches = [| [a; b] |];
      } ]
    | Enot (Eor (a, b, _), _) -> [ {
        nconc = [fm];
        nrule = NotOr (a, b);
        nprio = Prio.update prio sh_notor weight_alpha 0;
        branches = [| [enot (a); enot (b)] |];
      } ]
    | Enot (Eimply (a, b, _), _) -> [ {
        nconc = [fm];
        nrule = NotImpl (a, b);
        nprio = Prio.update prio sh_notimpl weight_alpha 0;
        branches = [| [a; enot (b)] |];
      } ]

    (* beta *)
    | Eor (a, b, _) -> [ {
        nconc = [fm];
        nrule = Or (a, b);
        nprio = Prio.update prio sh_or weight_beta 0;
        branches = [| [a]; [b] |];
      } ]
    | Eimply (a, b, _) -> [ {
        nconc = [fm];
        nrule = Impl (a, b);
        nprio = Prio.update prio sh_impl weight_beta 0;
        branches = [| [enot (a)]; [b] |];
      } ]
    | Enot (Eand (a, b, _), _) -> [ {
        nconc = [fm];
        nrule = NotAnd (a, b);
        nprio = Prio.update prio sh_notand weight_beta 0;
        branches = [| [enot (a)]; [enot (b)] |];
      } ]
    | Eequiv (a, b, _) -> [ {
        nconc = [fm];
        nrule = Equiv (a, b);
        nprio = Prio.update prio sh_equiv (weight_beta + weight_beta_double) 0;
        branches = [| [enot (a); enot (b)]; [a; b] |];
      } ]
    | Enot (Eequiv (a, b, _), _) -> [ {
        nconc = [fm];
        nrule = NotEquiv (a, b);
        nprio = Prio.update prio sh_notequiv
                            (weight_beta + weight_beta_double) 0;
        branches = [| [enot (a); b]; [a; enot (b)] |];
      } ]

    (* gamma *)
    | Eex (v, t, p, _) -> [ {
        nconc = [fm];
        nrule = Ex (fm);
        nprio = Prio.update prio sh_ex weight_gamma 0;
        branches = [| [Expr.substitute [(v, etau (v, t, p))] p] |];
      } ]
    | Enot (Eall (v, t, p, _), _) ->
      let np = enot (p) in
      [ {
        nconc = [fm];
        nrule = NotAll (fm);
        nprio = Prio.update prio sh_notall weight_gamma 0;
        branches = [| [Expr.substitute [(v, etau (v, t, np))] np] |];
      } ]

    (* delta (generalisation) *)
    | Eall (v, t, p, _) ->
      let w = emeta (fm) in
      [ {
        nconc = [fm];
        nrule = All (fm, w);
        nprio = Prio.update prio sh_all_meta weight_delta 0;
        branches = [| [Expr.substitute [(v, w)] p] |];
      } ]
    | Enot (Eex (v, t, p, _), _) ->
      let w = emeta (fm) in
      [ {
        nconc = [fm];
        nrule = NotEx (fm, w);
        nprio = Prio.update prio sh_notex_meta weight_delta 0;
        branches = [| [enot (Expr.substitute [(v, w)] p)] |];
      } ]

    (* unfolding definitions *)
    | Eapp (p, args, _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = substitute subst body in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end
    | Enot (Eapp (p, args, _), _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = enot (substitute subst body) in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end
    | Eapp ("=", [Eapp (p, args, _); e], _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = eapp ("=", [substitute subst body; e]) in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end
    | Eapp ("=", [e; Eapp (p, args, _)], _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = eapp ("=", [e; substitute subst body]) in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end
    | Enot (Eapp ("=", [Eapp (p, args, _); e], _), _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = enot (eapp ("=", [substitute subst body; e])) in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end
    | Enot (Eapp ("=", [e; Eapp (p, args, _)], _), _) when Index.has_def p ->
        begin try
          let (d, params, body) = Index.get_def p in
          let subst = List.map2 (fun x y -> (x,y)) params args in
          let unfolded = enot (eapp ("=", [e; substitute subst body])) in
          [ {
              nconc = [fm];
              nrule = Definition (d, fm, unfolded);
              nprio = Prio.update prio sh_def weight_def 0;
              branches = [| [unfolded] |];
          } ]
        with
        | Invalid_argument "List.map2" -> wrong_arity p
        | Not_found -> assert false
        end

    | Evar (v, _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = body in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]
    | Enot (Evar (v, _), _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = enot body in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]
    | Eapp ("=", [Evar (v, _); e], _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = eapp ("=", [body; e]) in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]
    | Eapp ("=", [e; Evar (v, _)], _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = eapp ("=", [e; body]) in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]
    | Enot (Eapp ("=", [Evar (v, _); e], _), _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = enot (eapp ("=", [body; e])) in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]
    | Enot (Eapp ("=", [e; Evar (v, _)], _), _) when Index.has_def v ->
        let (d, params, body) = Index.get_def v in
        let unfolded = enot (eapp ("=", [e; body])) in
        if params <> [] then wrong_arity v
        else [ {
          nconc = [fm];
          nrule = Definition (d, fm, unfolded);
          nprio = Prio.update prio sh_def weight_def 0;
          branches = [| [unfolded] |];
        } ]

    (* equality *)
    | Eapp ("=", [Emeta _; Emeta _], _) -> assert false (* done in refute *)
    | Eapp ("=", [(Emeta _ as e); f], _) -> rewrite prio e f f e
    | Eapp ("=", [e; (Emeta _ as f)], _) -> rewrite prio e f e f
    | Eapp ("=", [e1; e2], _) ->
        if Expr.equal e1 e2 then []
        else correlate_equal fm prio

    | Enot (Eapp ("=", [(Emeta (m1, _) as mm1); (Emeta (m2, _) as mm2)], _), _)
      ->
        let d1 = Index.get_meta m1 and d2 = Index.get_meta m2 in
        if d1 < d2
        then [make_inst m2 mm1 prio weight_metameta]
        else [make_inst m1 mm2 prio weight_metameta]

    | Enot (Eapp ("=", [Emeta (m, _); e], _), _) -> [make_inst m e prio 0]
    | Enot (Eapp ("=", [e; Emeta (m, _)], _), _) -> [make_inst m e prio 0]

    | Enot (Eapp ("=", [(Eapp (f1, a1, _) as e1);
                        (Eapp (f2, a2, _) as e2)], _), _)
      when f1 = f2 ->
        if List.length a1 = List.length a2 then begin
          [ {
              nconc = [fm];
              nrule = NotEqual (e1, e2);
              nprio = Prio.update prio sh_notequal weight_notequal 0;
              branches = make_inequals a1 a2;
          } ]
        end else begin
          if !Globals.warnings_flag then begin
            printf "add_nodes: variable arity ";
            Print.expr fm;
            printf "\n";
          end;
          []
        end
        @ correlate_noteq fm prio

    | Enot (Eapp ("=", [e1; e2], _), _) -> correlate_noteq fm prio

    | Enot (Eapp (s, _, _), _) ->
        let do_match p = make_notequiv p fm (Index.get_prio p) prio in
        List.map do_match (Index.find_pos s)

    | Eapp (s, _, _) ->
        let do_match p = make_notequiv fm p (Index.get_prio p) prio in
        List.map do_match (Index.find_neg s)

    | Evar (v, _) -> []            (* propositional variable *)
    | Enot (Evar (v, _), _) -> []  (* propositional variable *)

    | Etrue -> []
    | Enot (Efalse, _) -> []

    | Emeta _ | Etau _
    | Enot ((Emeta _ | Etau _), _) ->
        if !Globals.warnings_flag then begin
          printf "add_nodes: unexpected formula meta/tau";
          Print.expr fm;
          printf "\n";
        end;
        []

  in
  let add_node q n =
    Index.add_branches n.branches;
    Heap.insert q (add_size n)
  in
  List.fold_left add_node q (thnodes @@ newnodes)
;;

(* [diff l1 l2]
   return [l1] without the formulas present in [l2]
*)
let rec diff l1 l2 =
  match l1 with
  | [] -> []
  | e::t -> if List.exists (Expr.equal e) l2
            then diff t l2
            else e :: (diff t l2)
;;

(* [union l1 l2]
   return [l1 @ l2], removing duplicate formulas
*)
let union l1 l2 = (diff l1 l2) @ l2;;

(* [disjoint l1 l2]
   return true if [l1] and [l2] have no element in common
*)
let rec disjoint l1 l2 =
  match l1 with
  | [] -> true
  | h::t -> if List.exists (Expr.equal h) l2
            then false
            else disjoint t l2
;;

let order_nodes n1 n2 =
  let p1 = n1.sprio and p2 = n2.sprio in
  if p1.Prio.shape <> p2.Prio.shape then p1.Prio.shape - p2.Prio.shape
  else begin
    let crit2 = (p1.Prio.origin - p2.Prio.origin) * origin_ponderation
                + (p1.Prio.weight1 - p2.Prio.weight1) * weight_ponderation
                + (n1.ssize - n2.ssize) * size_ponderation
    in
    if crit2 <> 0 then crit2
    else p1.Prio.weight2 - p2.Prio.weight2
  end
;;

let rec reduce_list accu l =
  match l with
  | [] -> accu
  | Enot (Efalse, _) :: t -> reduce_list accu t
  | Eapp ("=", [e1; e2], _) :: t when Expr.equal e1 e2 -> reduce_list accu t
  | Eapp ("=", [e1; e2], _) as f :: t ->
     let g = eapp ("=", [e2; e1]) in
     if Index.member f || Index.member g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | Enot (Eapp ("=", [e1; e2], _), _) as f :: t ->
     let g = enot (eapp ("=", [e2; e1])) in
     if Index.member f || Index.member g
        || List.exists (Expr.equal f) accu || List.exists (Expr.equal g) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
  | f :: t ->
     if Index.member f || List.exists (Expr.equal f) accu
     then reduce_list accu t
     else reduce_list (f :: accu) t
;;

let reduce_branches n =
  let reduced = Array.map (reduce_list []) n.sbranches in
  let rec array_exists f a i =
    if i >= Array.length a then false
    else if f a.(i) then true
    else array_exists f a (i+1)
  in
  if array_exists (function [] -> true | _ -> false) reduced 0
  then None
  else Some { n with sbranches = reduced }
;;

let rec count_metas accu ee =
  match ee with
  | Evar _ -> accu
  | Emeta _ -> accu + 1
  | Eapp (_, args, _) -> List.fold_left count_metas accu args
  | Enot (e, _) -> count_metas accu e
  | Eand (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eor (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eimply (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Eequiv (e1, e2, _) -> count_metas (count_metas accu e1) e2
  | Etrue -> accu
  | Efalse -> accu
  | Eall (_, _, e, _) -> count_metas accu e
  | Eex (_, _, e, _) -> count_metas accu e
  | Etau (_, _, e, _) -> count_metas accu e
;;

let rec highest_meta accu = function
  | Evar _ -> accu
  | Emeta (e, _) -> max (Index.get_meta e) accu
  | Eapp (_, args, _) -> List.fold_left highest_meta accu args
  | Enot (e, _) -> highest_meta accu e
  | Eand (e1, e2, _) -> highest_meta (highest_meta accu e1) e2
  | Eor (e1, e2, _) -> highest_meta (highest_meta accu e1) e2
  | Eimply (e1, e2, _) -> highest_meta (highest_meta accu e1) e2
  | Eequiv (e1, e2, _) -> highest_meta (highest_meta accu e1) e2
  | Etrue -> accu
  | Efalse -> accu
  | Eall (_, _, e, _) -> highest_meta accu e
  | Eex (_, _, e, _) -> highest_meta accu e
  | Etau (_, _, e, _) -> highest_meta accu e
;;

let find_open_branch node state =
  let rec loop accu i =
    if i < 0 then accu
    else if state.(i) = Open then loop (i::accu) (i-1)
    else loop accu (i-1)
  in
  let open_branches = loop [] (Array.length state - 1) in
  match open_branches with
  | [] -> None
  | [i] -> Some i
  | l ->
      let rec loop best best_score l =
        match l with
        | [] -> Some best
        | i::t ->
            let s1 = Index.get_branches node.sbranches.(i) in
  (*
            let meta = List.fold_left good_meta false node.sbranches.(i) in
            let s2 = if meta then 1 else 0 in
            let s3 = - List.fold_left highest_meta 0 node.sbranches.(i) in
  *)
            let s5 = - List.fold_left count_metas 0 node.sbranches.(i) in
            let score = s1 + s5 in
            if score > best_score
            then loop i score t
            else loop best best_score t
      in loop (-1) (-1000000000) l
;;

let is_fruitless_inst n st =
  match n.srule, n.sbranches, st with
  | All _, [| [ e_con ] |], [| Back bl |] -> List.exists (Expr.equal e_con) bl
  | NotEx _, [| [ e_con ] |], [| Back bl |] -> List.exists (Expr.equal e_con) bl
  | _, _, _ -> false
;;

let good_lemma rule =
  match rule with
  | Close1 _ | Close2 _ | False | NotTrue | CloseEq _ -> false
  | _ -> true
;;

(* there is no Open in branches;
   if there are Back values, merge them
   else make a proof node
*)
let make_result n branches =
  let backs = ref []
  and has_back = ref false;
  and concs = ref []
  and proofs = ref [] in
  for i = 0 to Array.length branches - 1 do
    match branches.(i) with
    | Open -> assert false
    | Back l ->
        has_back := true;
        backs := union (diff l n.sbranches.(i)) !backs;
    | Closed p ->
        proofs := p :: !proofs;
        concs := union (diff p.mlconc n.sbranches.(i)) !concs;
  done;
  if not !has_back then begin
    assert (List.length !proofs = Array.length n.sbranches);
    let prf_node = {
      mlconc = union n.sconc !concs;
      mlrule = n.srule;
      mlhyps = Array.of_list (List.rev !proofs);
      mlrefc = 1;
    } in
    incr Globals.proof_nodes;
    if good_lemma n.srule then begin
      Index.add_proof prf_node;
    end;
    Closed prf_node
  end else begin
    Back (union n.sconc !backs)
  end
;;

let good_head q =
  match Heap.head q with
  | None -> true
  | Some node -> good_lemma node.srule
;;

let add_metas n =
  match n.srule with
  | All (p, Emeta (f, _)) | NotEx (p, Emeta (f, _)) when Expr.equal p f ->
      Index.add_meta f !cur_depth
  | _ -> ()
;;

exception NoProof;;

let rec refute_aux stk q forms =
  match forms with
  | [] ->
      if good_head q then begin
        match Index.search_proof () with
        | Some p -> p.mlrefc <- p.mlrefc + 1; unwind stk (Closed p)
        | None -> next_node stk q
      end else begin
        next_node stk q
      end
  | (Eapp ("=", [Emeta (m1, _); Emeta (m2, _)], _) as fm, _) :: fms ->
      if Expr.equal m1 m2
      then refute_aux stk q fms
      else unwind stk (Back [fm])
  | (fm, prio) as fp :: fms ->
      Index.add fm prio;
      Extension.add_formula fm prio;
      refute_aux stk (add_nodes q fp) fms

and refute stk q forms =
  Step.forms "refute" forms;
  refute_aux stk q forms

and next_node stk q =
  incr Globals.inferences;
  match Heap.remove q with
  | None -> raise NoProof
  | Some (n, q1) ->
      (* Step.rule "next_node" n.nrule; *)
      Index.remove_branches n.sbranches;
      let state = Array.make (Array.length n.sbranches) Open in
      match reduce_branches n with
      | Some n1 ->
          add_metas n1;
          next_branch false stk n1 q1 state
      | None -> next_node stk q1    (* FIXME add_branches count becomes wrong *)

and next_branch high_prio stk n q state =
  Step.rule "next_branch" n.srule;
  match find_open_branch n state with
  | Some i ->
      let fr = {node = n; queue = q; state = state; cur = i} in
      incr cur_depth;
      if !cur_depth > !top_depth then top_depth := !cur_depth;
      let with_prio e = (e, n.sprio) in
      refute (fr :: stk) q (List.map with_prio n.sbranches.(i))
  | None ->
      if is_fruitless_inst n state
      then next_node stk q
      else begin
        let result = make_result n state in
        unwind stk result
      end

and unwind stk res =
  match stk with
  | [] -> res
  | fr :: stk1 ->
      Step.rule "unwind" fr.node.srule;
      let f x = Extension.remove_formula x; Index.remove x in
      List.iter f (List.rev fr.node.sbranches.(fr.cur));
      begin match fr.node.srule with
      | All (p, Emeta (f, _)) | NotEx (p, Emeta (f, _)) when Expr.equal p f ->
          Index.remove_meta f;
      | _ -> ()
      end;
      decr cur_depth;
      begin match res with
      | Closed p when disjoint fr.node.sbranches.(fr.cur) p.mlconc ->
          unwind stk1 res
      | Back l when disjoint fr.node.sbranches.(fr.cur) l ->
          unwind stk1 res
      | Closed _ ->
          fr.state.(fr.cur) <- res;
          next_branch true stk1 fr.node fr.queue fr.state
      | Back _ ->
          fr.state.(fr.cur) <- res;
          next_branch false stk1 fr.node fr.queue fr.state
      | Open -> assert false
      end;
;;

let rec reduce_initial_list accu l =
  match l with
  | [] -> accu
  | (f, p) as fp :: t ->
      if List.exists (fun (x,_) -> Expr.equal f x) accu
      then reduce_initial_list accu t
      else reduce_initial_list (fp :: accu) t
;;

let ticker () =
  let tm = Sys.time () in
  let heap_size = (Gc.stat ()).Gc.heap_words in  (* FIXME use Gc.quick_stat *)
  Globals.do_progress begin fun () ->
    eprintf "depth %5d/%d  search %d  proof %d  \
             lemma %d  size %dM  time %.0f\n"
            !cur_depth !top_depth !Globals.inferences !Globals.proof_nodes 
            !Globals.stored_lemmas (heap_size / 1_000_000) tm;
  end;
  if tm > !Globals.time_limit then begin
    eprintf " time limit exceeded\n";
    flush stderr;
    raise NoProof;
  end;
  if float heap_size > !Globals.size_limit then begin
    eprintf " size limit exceeded\n";
    flush stderr;
    raise NoProof;
  end;
;;

let prove defs l =
  try
    List.iter Index.add_def defs;
    let al = Gc.create_alarm ticker in
    let rl = reduce_initial_list [] l in
    let give_prio (fm, orig) = (fm, Prio.make orig) in
    let pl = List.map give_prio l in
    Globals.inferences := 0;
    Globals.proof_nodes := 0;
    cur_depth := 0;
    top_depth := 0;
    let result = refute [] (Heap.empty order_nodes) pl in
    Gc.delete_alarm al;
    ticker ();
    Globals.end_progress "";
    match result with
    | Closed p -> p
    | Back _ -> assert false
    | Open -> assert false
  with NoProof ->
    Globals.end_progress " search failed";
    raise NoProof
;;
