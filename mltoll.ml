(*  Copyright 2004 INRIA  *)
Version.add "$Id: mltoll.ml,v 1.10 2004-09-28 13:12:58 doligez Exp $";;

open Expr;;
open Misc;;
open Mlproof;;
open Printf;;

module LL = Llproof;;

let lemma_num = ref 0;;
let lemma_list = ref [];;

let lemma_name n = sprintf "lemma_%d" n;;

let make_tau_name p = sprintf "_T_%d" (Index.get_number p);;
let make_any_name p = sprintf "_Z_%d" (Index.get_number p);;

(* FIXME TODO: memoifier tr_term et tr_prop (?) *)

let rec tr_term t =
  match t with
  | Evar (v, _) -> t
  | Emeta (e, _) -> evar (make_any_name e)
  | Eapp (s, es, _) -> eapp (s, List.map tr_term es)
  | Etau _ -> evar (make_tau_name t)
  | _ -> assert false
;;

let rec tr_prop a =
  match a with
  | Evar (v, _) -> a
  | Emeta _ -> assert false
  | Eapp (s, args, _) -> eapp (s, List.map tr_term args)

  | Enot (p, _) -> enot (tr_prop p)
  | Eand (p, q, _) -> eand (tr_prop p, tr_prop q)
  | Eor (p, q, _) -> eor (tr_prop p, tr_prop q)
  | Eimply (p, q, _) -> eimply (tr_prop p, tr_prop q)
  | Eequiv (p, q, _) -> eequiv (tr_prop p, tr_prop q)
  | Etrue -> etrue
  | Efalse -> efalse
  | Eall (v, t, e, _) -> eall (v, t, tr_prop e)
  | Eex (v, t, e, _) -> eex (v, t, tr_prop e)

  | Etau _ -> assert false
;;

let tr_rule r =
  match r with
  | Close (p) -> LL.Raxiom (tr_prop p)
  | Close_refl ("=", e) -> LL.Rnoteq (tr_term e)
  | False -> LL.Rfalse
  | NotTrue -> LL.Rnottrue
  | NotNot (p) -> LL.Rnotnot (tr_prop p)
  | And (p, q) -> LL.Rconnect (LL.And, tr_prop p, tr_prop q)
  | NotOr (p, q) -> LL.Rnotconnect (LL.Or, tr_prop p, tr_prop q)
  | NotImpl (p, q) -> LL.Rnotconnect (LL.Imply, tr_prop p, tr_prop q)
  | NotAll (Enot (Eall (v, t, p, _) as pp, _)) ->
      LL.Rnotall (tr_prop pp, make_tau_name (etau (v, t, enot (p))))
  | NotAll _ -> assert false
  | Ex (Eex (v, t, p, _) as pp) ->
      LL.Rex (tr_prop pp, make_tau_name (etau (v, t, p)))
  | Ex _ -> assert false
  | All (p, t) -> LL.Rall (tr_prop p, tr_term t)
  | NotEx (Enot (p, _) as e2, t) -> LL.Rnotex (tr_prop p, tr_term t)
  | NotEx _ -> assert false
  | Or (p, q) -> LL.Rconnect (LL.Or, tr_prop p, tr_prop q)
  | Impl (p, q) -> LL.Rconnect (LL.Imply, tr_prop p, tr_prop q)
  | NotAnd (p, q) -> LL.Rnotconnect (LL.And, tr_prop p, tr_prop q)
  | Equiv (p, q) -> LL.Rconnect (LL.Equiv, tr_prop p, tr_prop q)
  | NotEquiv (p, q) -> LL.Rnotconnect (LL.Equiv, tr_prop p, tr_prop q)
  | P_NotP (Eapp ("=", [t1; t2], _), Enot (Eapp ("=", [t3; t4], _), _)) ->
      LL.Requalnotequal (tr_term t1, tr_term t2, tr_term t3, tr_term t4)
  | P_NotP (p, q) -> LL.Rpnotp (tr_prop p, tr_prop q)
  | P_NotP_sym ("=", Eapp ("=", [t1; t2], _), Enot (Eapp ("=", [t3; t4], _), _))
      -> LL.Requalnotequal (tr_term t1, tr_term t2, tr_term t3, tr_term t4)
  | P_NotP_sym ("=", _, _) -> assert false
  | NotEqual (e1, e2) -> LL.Rnotequal (tr_term e1, tr_term e2)

  | Definition (DefReal _, folded, unfolded) ->
      LL.Rdefinition (tr_prop folded, tr_prop unfolded)

  | Cut (p) -> LL.Rcut (p)

  (* derived rules, handled by translate_derived: *)
  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | Ext _
  | Close_sym _
  | Refl _
  | Trans _
  | Definition (DefPseudo _, _, _)
    -> assert false

  | P_NotP_sym (s, _, _) (* when s <> "=" *) -> assert false
  | Close_refl (s, _) (* when s <> "=" *) -> assert false
;;

let rec merge l1 l2 =
  match l1 with
  | [] -> l2
  | (v,t) as vt :: vts ->
      if List.mem_assoc v l2
      then merge vts l2
      else merge vts (vt :: l2)
;;

let rec get_params accu p =
  match p with
  | Evar (v, _) -> accu
  | Emeta (Eall (v, t, _, _) as p, _) -> merge [(make_any_name p, t)] accu
  | Emeta (Enot (Eex (v, t, _, _), _) as p, _) ->
      merge [(make_any_name p, t)] accu
  | Emeta _ -> assert false
  | Eapp (_, es, _) -> List.fold_left get_params accu es

  | Enot (e, _) -> get_params accu e
  | Eand (e, f, _) -> get_params (get_params accu e) f
  | Eor (e, f, _) -> get_params (get_params accu e) f
  | Eimply (e, f, _) -> get_params (get_params accu e) f
  | Eequiv (e, f, _) -> get_params (get_params accu e) f
  | Etrue -> accu
  | Efalse -> accu
  | Eall (v, t, e, _) -> get_params accu e
  | Eex (v, t, e, _) -> get_params accu e
  | Etau (v, t, _, _) -> merge [(make_tau_name p, t)] accu
;;

let lemma_tbl = (Hashtbl.create 997
                 : (string, LL.lemma * Expr.expr list) Hashtbl.t);;

let get_lemma p =
  let name = lemma_name (-p.mlrefc) in
  let (lemma, extras) = Hashtbl.find lemma_tbl name in
  let args = List.map fst lemma.LL.params in
  ({
    LL.conc = lemma.LL.proof.LL.conc;
    LL.rule = LL.Rlemma (lemma.LL.name, args);
    LL.hyps = [];
  }, extras)
;;

let make_lemma llprf extras mlprf =
  incr lemma_num;
  let name = (lemma_name !lemma_num) in
  mlprf.mlrefc <- - !lemma_num;
  let l = {
    LL.name = name;
    LL.params = List.fold_left get_params [] mlprf.mlconc;
    LL.proof = llprf;
  } in
  Hashtbl.add lemma_tbl name (l, extras);
  lemma_list := l :: !lemma_list;
;;

let is_derived = function
  | Close_refl ("=", _) -> false
  | Close_refl (_, _) -> true

  | P_NotP_sym ("=", _, _) -> false
  | P_NotP_sym (_, _, _) -> true

  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | Ext _
  | Close_sym _
  | Refl _
  | Trans _
  | Definition (DefPseudo _, _, _)
    -> true

  | _ -> false
;;

let remove f l = Expr.diff l [f];;

let rec recomp_conj sub extras f =
  match f with
  | Eand (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1) = recomp_conj sub extras a in
      let (n2, ext2) = recomp_conj n1 ext1 b in
      let nn = {
          LL.conc = tr_prop f :: diff n2.LL.conc [la; lb];
          LL.rule = LL.Rconnect (LL.And, la, lb);
          LL.hyps = [n2];
        }
      in (nn, diff ext2 [f])
  | Enot (a, _) -> recomp_conj_n sub extras a
  | _ -> (sub, extras)

and recomp_conj_n sub extras f =
  match f with
  | Eor (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1) = recomp_conj_n sub extras a in
      let (n2, ext2) = recomp_conj_n n1 ext1 b in
      let nn = {
          LL.conc = enot (tr_prop f) :: diff n2.LL.conc [enot la; enot lb];
          LL.rule = LL.Rnotconnect (LL.Or, la, lb);
          LL.hyps = [n2];
        }
      in (nn, diff ext2 [enot f])
  | Eimply (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1) = recomp_conj sub extras a in
      let (n2, ext2) = recomp_conj_n n1 ext1 b in
      let nn = {
          LL.conc = enot (tr_prop f) :: diff n2.LL.conc [la; enot lb];
          LL.rule = LL.Rnotconnect (LL.Imply, la, lb);
          LL.hyps = [n2];
        }
      in (nn, diff ext2 [enot f])
  | Enot (a, _) ->
      let la = tr_prop a in
      let (n1, ext1) = recomp_conj sub extras a in
      let nn = {
          LL.conc = enot (tr_prop f) :: diff n1.LL.conc [la];
          LL.rule = LL.Rnotnot (la);
          LL.hyps = [n1];
        }
      in (nn, diff ext1 [enot f])
  | _ -> (sub, extras)
;;

let rec recomp_disj sub f =
  match f with
  | Eor (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1, sub1) = recomp_disj sub a in
      let c1 = diff n1.LL.conc [la] in
      let (n2, ext2, sub2) = recomp_disj sub1 b in
      let c2 = diff n2.LL.conc [lb] in
      let nn = {
          LL.conc = tr_prop f :: (union c1 c2);
          LL.rule = LL.Rconnect (LL.Or, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, diff (union ext1 ext2) [f], sub2)
  | Eimply (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1, sub1) = recomp_disj_n sub a in
      let c1 = remove (enot la) n1.LL.conc in
      let (n2, ext2, sub2) = recomp_disj sub1 b in
      let c2 = remove lb n2.LL.conc in
      let nn = {
          LL.conc = tr_prop f :: (union c1 c2);
          LL.rule = LL.Rconnect (LL.Imply, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, diff (union ext1 ext2) [f], sub2)
  | Enot (a, _) -> recomp_disj_n sub a
  | _ ->
     begin match sub with
     | (node, ext) :: rest -> (node, ext, rest)
     | [] -> assert false
     end

and recomp_disj_n sub f =
  match f with
  | Eand (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, ext1, sub1) = recomp_disj_n sub a in
      let c1 = remove (enot la) n1.LL.conc in
      let (n2, ext2, sub2) = recomp_disj_n sub1 b in
      let c2 = remove (enot lb) n2.LL.conc in
      let nn = {
          LL.conc = enot (tr_prop f) :: (union c1 c2);
          LL.rule = LL.Rnotconnect (LL.And, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, diff (union ext1 ext2) [enot f], sub2)
  | Enot (a, _) ->
      let la = tr_prop a in
      let (n1, ext1, sub1) = recomp_disj sub a in
      let c1 = remove la n1.LL.conc in
      let nn = {
          LL.conc = enot (tr_prop f) :: c1;
          LL.rule = LL.Rnotnot (la);
          LL.hyps = [n1];
        }
      in (nn, diff ext1 [enot f], sub1)
  | _ ->
     begin match sub with
     | (node, ext) :: rest -> (node, ext, rest)
     | [] -> assert false
     end
;;

exception Found of Expr.expr;;

let rec xfind_occ v e1 e2 =
  match e1, e2 with
  | Evar (v1, _), _ when Expr.equal e1 v -> raise (Found e2)
  | Emeta _, _ -> ()
  | Eapp (_, a1, _), Eapp (_, a2, _) -> List.iter2 (xfind_occ v) a1 a2
  | Enot (f1, _), Enot (f2, _) -> xfind_occ v f1 f2
  | Eand (f1, g1, _), Eand (f2, g2, _) -> xfind_occ v f1 f2; xfind_occ v g1 g2
  | Eor (f1, g1, _), Eor (f2, g2, _) -> xfind_occ v f1 f2; xfind_occ v g1 g2
  | Eimply (f1, g1, _), Eimply (f2, g2, _) ->
      xfind_occ v f1 f2; xfind_occ v g1 g2
  | Eequiv (f1, g1, _), Eequiv (f2, g2, _) ->
      xfind_occ v f1 f2; xfind_occ v g1 g2
  | Efalse, _ -> ()
  | Eall (v1, _, _, _), _ when Expr.equal v1 v -> ()
  | Eall (_, _, f1, _), Eall (_, _, f2, _) -> xfind_occ v f1 f2
  | Eex (v1, _, _, _), _ when Expr.equal v1 v -> ()
  | Eex (_, _, f1, _), Eex (_, _, f2, _) -> xfind_occ v f1 f2
  | Etau _, _ -> ()
  | _ -> assert false
;;

let find_occ v e1 e2 =
  try xfind_occ v e1 e2;
      assert false
  with Found e -> e
;;

let find_subst e1 e2 =
  match e1, e2 with
  | Eall (v1, _, f1, _), Eall (v2, _, f2, _) -> (v2, find_occ v1 f1 f2)
  | Eex (v1, _, f1, _), Eex (v2, _, f2, _) -> (v2, find_occ v1 f1 f2)
  | _, _ -> assert false
;;

let rec get_actuals env var =
  match var with
  | [] -> []
  | (v, fm) :: rest ->
      let act =
        if List.mem_assoc v rest then emeta (fm) else
        begin try List.assoc v env
        with Not_found -> emeta (fm)
        end
      in
      act :: (get_actuals env rest)
;;

let rec find_diff f1 f2 =
  match f1, f2 with
  | Enot (g1, _), Enot (g2, _) -> find_diff g1 g2
  | Eapp (s1, [g1; h1], _), Eapp (s2, [g2; h2], _) when s1 = s2 ->
      if Expr.equal g1 g2 then find_diff h1 h2
      else (assert (Expr.equal h1 h2); find_diff g1 g2)
  | Eapp (s1, args1, _), _ -> args1
  | Evar _, _ -> []
  | _ -> assert false
;;

let rec get_univ f =
  match f with
  | Eall (v, ty, body, _) -> (v, f) :: get_univ body
  | _ -> []
;;

let get_args def args folded unfolded =
  let vals = find_diff folded unfolded in
  let env = List.combine args vals in
  let vars = get_univ def in
  get_actuals env vars
;;

let inst_all e f =
  match e with
  | Eall (v, t, e1, _) -> Expr.substitute [(v, f)] e1
  | _ -> assert false
;;

let rec make_vars n =
  if n = 0 then [] else Expr.newvar () :: make_vars (n-1)
;;

let rec add_foralls vs e =
  match vs with
  | [] -> e
  | h::t -> eall (h, "?", add_foralls t e)
;;

let rec add_exists vs e =
  match vs with
  | [] -> e
  | h::t -> eex (h, "?", add_exists t e)
;;

let rec decompose_forall e v p naxyz arity f args =
  if arity = 0 then begin
    let fttt = eapp (f, args) in
    let pfttt = substitute [(v, fttt)] p in
    let n1 = make_node [pfttt; naxyz] (Close pfttt) [] [] in
    let n2 = make_node [e; naxyz] (All (e, fttt)) [[pfttt]] [n1] in
    n2
  end else begin
    match naxyz with
    | Enot (Eall (v1, t1, p1, _), _) ->
        let tau = etau (v1, t1, enot p1) in
        let nayz = enot (substitute [(v1, tau)] p1) in
        let n1 = decompose_forall e v p nayz (arity-1) f (args @ [tau]) in
        let n2 = make_node [naxyz] (NotAll naxyz) [[nayz]] [n1] in
        n2
    | _ -> assert false
  end
;;

let rec decompose_exists e v p exyz arity f args =
  if arity = 0 then begin
    let fttt = eapp (f, args) in
    let npfttt = enot (substitute [(v, fttt)] p) in
    let n1 = make_node [npfttt; exyz] (Close exyz) [] [] in
    let n2 = make_node [e; exyz] (NotEx (e, fttt)) [[npfttt]] [n1] in
    n2
  end else begin
    match exyz with
    | Eex (v1, t1, p1, _) ->
        let tau = etau (v1, t1, p1) in
        let eyz = substitute [(v1, tau)] p1 in
        let n1 = decompose_exists e v p eyz (arity-1) f (args @ [tau]) in
        let n2 = make_node [exyz] (Ex exyz) [[eyz]] [n1] in
        n2
    | _ -> assert false
  end
;;

let rec to_llproof p =
  if p.mlrefc < 0 then
    get_lemma p
  else begin
    let (result, extras) =
      if is_derived p.mlrule
      then translate_derived p
      else
        let (subproofs, subextras) = get_sub (Array.to_list p.mlhyps) in
        let extras = diff subextras p.mlconc in
        ({
          LL.conc = List.map tr_prop (extras @@ p.mlconc);
          LL.rule = tr_rule p.mlrule;
          LL.hyps = subproofs;
        }, extras)
    in
    if p.mlrefc > 1 then begin
      make_lemma result extras p;
      get_lemma p
    end else begin
      (result, extras)
    end
  end

and get_sub l =
  match l with
  | [] -> ([], [])
  | h::t ->
      let (sub, ext) = to_llproof h in
      let (subs, exts) = get_sub t in
      (sub :: subs, union ext exts)

and translate_derived p =
  match p.mlrule with
  | Definition (DefPseudo ((def_hyp, _), s, args, body), folded, unfolded) ->
      let actuals = get_args def_hyp args folded unfolded in
      let exp =
        translate_pseudo_def p def_hyp s actuals body folded unfolded
      in
      let (n, ext) = to_llproof exp in
      (n, union [def_hyp] ext)
  | ConjTree (e) ->
      assert (Array.length p.mlhyps = 1);
      let (sub, extras) = to_llproof p.mlhyps.(0) in
      recomp_conj sub extras e
  | DisjTree (e) ->
      let sub = List.map to_llproof (Array.to_list p.mlhyps) in
      let (node, extras, subs) = recomp_disj sub e in
      assert (subs = []);
      (node, extras)
  | AllPartial ((Eall (v1, t1, q, _) as e1), f, arity) ->
      let n1 = match p.mlhyps with
        | [| n1 |] -> n1
        | _ -> assert false
      in
      let vs = make_vars arity in
      let sxyz = eapp (f, vs) in
      let axyz = add_foralls vs (substitute [(v1, sxyz)] q) in
      let naxyz = enot (axyz) in
      let n2 = decompose_forall e1 v1 q naxyz arity f [] in
      let n3 = make_node [] (Cut axyz) [[axyz]; [naxyz]] [n1; n2] in
      to_llproof n3
  | NotExPartial ((Enot ((Eex (v1, t1, q, _) as e1), _) as ne1), f, arity) ->
      let n1 = match p.mlhyps with
        | [| n1 |] -> n1
        | _ -> assert false
      in
      let vs = make_vars arity in
      let sxyz = eapp (f, vs) in
      let exyz = add_exists vs (substitute [(v1, sxyz)] q) in
      let nexyz = enot (exyz) in
      let n2 = decompose_exists ne1 v1 q exyz arity f [] in
      let n3 = make_node [] (Cut exyz) [[exyz]; [nexyz]] [n2; n1] in
      to_llproof n3
  | Close_sym ("=", a, b) ->
      let aeb = eapp ("=", [a; b]) in
      let nbea = enot (eapp ("=", [b; a])) in
      let naea = enot (eapp ("=", [a; a])) in
      let nbeb = enot (eapp ("=", [b; b])) in
      let n1 = make_node [naea] (Close_refl ("=", a)) [] [] in
      let n2 = make_node [nbeb] (Close_refl ("=", b)) [] [] in
      let n3 = make_node [aeb; nbea] (P_NotP_sym ("=", aeb, nbea))
                         [[nbeb]; [naea]] [n2; n1]
      in
      to_llproof n3
  | Close_sym (s, a, b) ->
      let sym_hyp = Eqrel.get_sym_hyp s in
      let pab = eapp (s, [a; b]) in
      let npab = enot pab in
      let pba = eapp (s, [b; a]) in
      let npba = enot pba in
      let pabipba = eimply (pab, pba) in
      let aypayipya = inst_all sym_hyp a in
      let n1 = make_node [pab; npab] (Close pab) [] [] in
      let n2 = make_node [pba; npba] (Close pba) [] [] in
      let n3 = make_node [pabipba] (Impl (pab, pba)) [[npab]; [pba]] [n1; n2] in
      let n4 = make_node [aypayipya] (All (aypayipya, b)) [[pabipba]] [n3] in
      let n5 = make_node [sym_hyp] (All (sym_hyp, a)) [[aypayipya]] [n4] in
      let (n, ext) = to_llproof n5 in
      (n, union [sym_hyp] ext)
  | Close_refl (s, a) ->
      let refl_hyp = Eqrel.get_refl_hyp s in
      let paa = eapp (s, [a; a]) in
      let n1 = make_node [paa; enot paa] (Close paa) [] [] in
      let n2 = make_node [refl_hyp] (All (refl_hyp, a)) [[paa]] [n1] in
      let (n, ext) = to_llproof n2 in
      (n, union [refl_hyp] ext)
  | P_NotP_sym (s, (Eapp (s1, [a; b], _) as pab), (Eapp (s2, [c; d], _) as pcd))
    when s = s1 && s = s2 ->
      let (n1, n2) = match p.mlhyps with
        | [| n1; n2 |] -> (n1, n2)
        | _ -> assert false
      in
      let sym_hyp = Eqrel.get_sym_hyp s in
      let pba = eapp (s, [b; a]) in
      let npcd = enot pcd in
      let nbec = enot (eapp ("=", [b; c])) in
      let naed = enot (eapp ("=", [a; d])) in
      let npab = enot pab in
      let pabipba = eimply (pab, pba) in
      let aypayipya = inst_all sym_hyp a in
      let n3 = make_node [npab; pab] (Close pab) [] [] in
      let n4 = make_node [pba; npcd] (P_NotP (pba, npcd))
                         [[nbec]; [naed]] [n1; n2]
      in
      let n5 = make_node [pabipba] (Impl (pab, pba)) [[npab]; [pba]] [n3; n4] in
      let n6 = make_node [aypayipya] (All (aypayipya, b)) [[pabipba]] [n5] in
      let n7 = make_node [sym_hyp] (All (sym_hyp, a)) [[aypayipya]] [n6] in
      let (n, ext) = to_llproof n7 in
      (n, union [sym_hyp] ext)
  | Refl (s, a, b) ->
      let n1 = match p.mlhyps with
        | [| n1 |] -> n1
        | _ -> assert false
      in
      let refl_hyp = Eqrel.get_refl_hyp s in
      let paa = eapp (s, [a; a]) in
      let npab = enot (eapp (s, [a; b])) in
      let naea = enot (eapp ("=", [a; a])) in
      let naeb = enot (eapp ("=", [a; b])) in
      let n2 = make_node [naea] (Close_refl (s, a)) [] [] in
      let n3 = make_node [paa; npab] (P_NotP (paa, npab))
                         [[naea]; [naeb]] [n2; n1]
      in
      let n4 = make_node [refl_hyp] (All (refl_hyp, a)) [[paa]] [n3] in
      let (n, ext) = to_llproof n4 in
      (n, union [refl_hyp] ext)
  | Trans (side, sym, Enot (Eapp (s, [a; b], _), _), Eapp ("=", [c; d], _)) ->
      translate_trans_equal side sym s a b c d p
  | Trans (side, sym, Enot (Eapp (s1, [a; b], _), _), Eapp (s2, [c; d], _))
    when s1 = s2 ->
      translate_trans side sym s1 a b c d p
  | Trans _ -> assert false
  | Ext _ ->
      let sub = Array.map to_llproof p.mlhyps in
      Extension.to_llproof tr_prop tr_term p sub

  | _ -> assert false

and translate_trans_equal side sym p a b c d prnode =
  let (x, y, z, t, u, v, cross1, cross2) =
    match side, sym with
    | L, false -> d, b, b, c, a, d, false, false
    | R, false -> a, c, a, d, b, c, true,  true
    | L, true  -> a, d, a, c, b, d, true,  false
    | R, true  -> c, b, b, d, a, c, false, true
  in
  let (n1, n2) =
    match prnode.mlhyps with
    | [| n1; n2 |] -> (n1, n2)
    | _ -> assert false
  in
  let ced = eapp ("=", [c; d]) in
  let pxy = eapp (p, [x; y]) in
  let npab = enot (eapp (p, [a; b])) in
  let nvev = enot (eapp ("=", [v; v])) in
  let nveu = enot (eapp ("=", [v; u])) in
  let nteu = enot (eapp ("=", [t; u])) in
  let nzez = enot (eapp ("=", [z; z])) in
  let nxea = enot (eapp ("=", [x; a])) in
  let nyeb = enot (eapp ("=", [y; b])) in
  let n3 = make_node [nvev] (Close_refl ("=", v)) [] [] in
  let rule4 = if cross2 then (P_NotP (ced, nveu))
                        else (P_NotP_sym (p, ced, nveu))
  in
  let n4 = make_node [nveu; ced] rule4 [[nvev]; [nteu]] [n3; n1] in
  let n5 = make_node [nzez] (Close_refl ("=", z)) [] [] in
  let subs6 = if cross1 then [n5; n4] else [n4; n5] in
  let n6 = make_node [pxy; npab] (P_NotP (pxy, npab)) [[nxea]; [nyeb]] subs6 in
  let n7 = make_node [] (Cut pxy) [[pxy]; [enot pxy]] [n6; n2] in
  to_llproof n7

and translate_trans side sym p a b c d prnode =
  let trans_hyp = Eqrel.get_trans_hyp p in
  let ty = match trans_hyp with
           | Eall (_, ty, _, _) -> ty
           | _ -> assert false
  in
  let (u, v, w, x, y, z, t, cross1, cross2) =
    match side, sym with
    | L, false -> (d, c, a, a, d, a, d, false, false)
    | R, false -> (c, d, b, c, b, c, b, true, true)
    | L, true -> (d, c, b, d, b, b, d, true, false)
    | R, true -> (c, d, a, a, c, c, a, false, true)
  in
  let (n1, n2) =
    match prnode.mlhyps with
    | [| n1; n2 |] -> (n1, n2)
    | _ -> assert false
  in
  let pab = eapp (p, [a; b]) in
  let pcd = eapp (p, [c; d]) in
  let nueu = enot (eapp ("=", [u; u])) in
  let pzt = eapp (p, [z; t]) in
  let npzt = enot pzt in
  let pau = eapp (p, [a; u]) in
  let pub = eapp (p, [u; b]) in
  let nvew = enot (eapp ("=", [v; w])) in
  let n4 =
    if Expr.equal pzt pcd then (
      make_node [npzt; pcd] (Close pcd) [] []
    ) else (
      let n3 = make_node [nueu] (Close_refl ("=", u)) [] [] in
      let hyps4 = if cross2 then [[nueu]; [nvew]] else [[nvew]; [nueu]] in
      let subs4 = if cross2 then [n3; n1] else [n1; n3] in
      let n4 = make_node [npzt; pcd] (P_NotP (pcd, npzt)) hyps4 subs4 in
      n4
    )
  in
  let (n8, sym_hyps) =
    if sym then (
      let sym_hyp = Eqrel.get_sym_hyp p in
      let ptz = eapp (p, [t; z]) in
      let n5 = make_node [ptz; enot ptz] (Close ptz) [] [] in
      let pztiptz = eimply (pzt, ptz) in
      let n6 = make_node [pztiptz] (Impl (pzt, ptz)) [[npzt]; [ptz]] [n4; n5] in
      let akpzkipkz = inst_all sym_hyp z in
      let n7 = make_node [akpzkipkz] (All (akpzkipkz, t)) [[pztiptz]] [n6] in
      let n8 = make_node [sym_hyp] (All (sym_hyp, z)) [[akpzkipkz]] [n7] in
      (n8, [sym_hyp])
    ) else (
      (n4, [])
    )
  in
  let n9 = make_node [pab; enot pab] (Close pab) [] [] in
  let subs10 = if cross1 then [n8; n9] else [n2; n9] in
  let pubipab = eimply (pub, pab) in
  let n10 = make_node [pubipab] (Impl (pub, pab)) [[enot pub]; [pab]] subs10 in
  let subs11 = if cross1 then [n2; n10] else [n8; n10] in
  let pauipubipab = eimply (pau, pubipab) in
  let n11 = make_node [pauipubipab] (Impl (pau, pubipab))
                      [[enot pau]; [pubipab]] subs11
  in
  let alakpaliplkipak = inst_all trans_hyp a in
  let akpauipukipak = inst_all alakpaliplkipak u in
  let n12 = make_node [akpauipukipak] (All (akpauipukipak, b))
                      [[pauipubipab]] [n11]
  in
  let n13 = make_node [alakpaliplkipak] (All (alakpaliplkipak, u))
                      [[akpauipukipak]] [n12]
  in
  let n14 = make_node [trans_hyp] (All (trans_hyp, a)) [[alakpaliplkipak]] [n13]
  in
  let (n, ext) = to_llproof n14 in
  (n, union (trans_hyp :: sym_hyps) ext)

and translate_pseudo_def p def_hyp s args body folded unfolded =
  match args with
  | [] -> translate_pseudo_def_base p def_hyp s body folded unfolded
  | a1::rest ->
      let newhyp = inst_all def_hyp a1 in
      let n1 = translate_pseudo_def p newhyp s rest body folded unfolded in
      make_node [def_hyp] (All (def_hyp, a1)) [[newhyp]] [n1]

and translate_pseudo_def_base p def_hyp s body folded unfolded =
  let n1 = match p.mlhyps with
    | [| n1 |] -> n1
    | _ -> assert false
  in
  match def_hyp with
  | Eequiv (a, b, _) ->
      let (q, nq, unf, nunf, cross) = match folded, unfolded with
        | Enot (q, _), Enot (unf, _) -> (q, folded, unf, unfolded, true)
        | q, unf -> (q, enot q, unf, enot unf, false)
      in
      let n2 = make_node [q; nq] (Close q) [] [] in
      if cross then
        make_node [def_hyp] (Equiv (q, unf)) [[nunf]; [q]] [n1; n2]
      else
        make_node [def_hyp] (Equiv (q, unf)) [[nq]; [unf]] [n2; n1]
  | Eapp ("=", [_; _], _) when Expr.equal folded (enot def_hyp) ->
      make_node [folded; def_hyp] (Close def_hyp) [] []
  | Eapp ("=", [_; _], _) ->
      let (cross1, negunf, baseunf) = match unfolded with
        | Enot (neg, _) -> (true, neg, neg)
        | _ -> (false, enot unfolded, unfolded)
      in
      let (sym, f, body) = match def_hyp with
        | Eapp ("=", [Eapp (s1, _, _) as f; body], _)
        | Eapp ("=", [Evar (s1, _) as f; body], _)
          when s1 = s -> (cross1, f, body)
        | Eapp ("=", [body; Eapp (s1, _, _) as f], _)
        | Eapp ("=", [body; Evar (s1, _) as f], _)
          when s1 = s -> (not cross1, f, body)
        | _ -> assert false
      in
      let (cross2, e) = match (folded, unfolded) with
        | Eapp (_, [f1; f2], _), Eapp (_, [u1; u2], _)
        | Enot (Eapp (_, [f1; f2], _), _), Enot (Eapp (_, [u1; u2], _), _)
           -> if Expr.equal f1 u1 then (true, f1)
              else (assert (Expr.equal f2 u2); (false, f2))
        | _ -> assert false
      in
      let (x, y) = if cross1 then (body, f) else (f, body) in
      let nfeb = enot (eapp ("=", [x; y])) in
      let neee = enot (eapp ("=", [e; e])) in
      let rule2 = if sym then Close_sym ("=", y, x) else Close def_hyp in
      let n2 = make_node [nfeb; def_hyp] rule2 [] [] in
      let n3 = make_node [neee] (Close_refl ("=", e)) [] [] in
      let hyps4 = if cross2 then [[neee]; [nfeb]] else [[nfeb]; [neee]] in
      let subs4 = if cross2 then [n3; n2] else [n2; n3] in
      let rule4 = if cross1 then P_NotP (baseunf, folded)
                            else P_NotP (folded, baseunf)
      in
      let n4 = make_node [negunf; folded] rule4 hyps4 subs4 in
      if cross1
        then make_node [] (Cut baseunf) [[baseunf]; [enot baseunf]] [n4; n1]
        else make_node [] (Cut baseunf) [[baseunf]; [enot baseunf]] [n1; n4]
  | _ -> assert false
;;

let rec charged_extra phrases e =
  match phrases with
  | [] -> true
  | Phrase.Hyp (_, f, _) :: _ when Expr.equal e f -> false
  | _ :: rest -> charged_extra rest e
;;

let discharge_extra ll e =
  let (p, relhyps) = Eqrel.get_proof e in
  let (lp, extras) = to_llproof p in
  assert (extras = []);
  let le = tr_prop e in
  let lrelhyps = List.map tr_prop relhyps in
  {
    LL.conc = union lrelhyps (diff ll.LL.conc [le]);
    LL.rule = LL.Rcut (le);
    LL.hyps = [ll; lp];
  }
;;

let translate th_name phrases p =
  lemma_num := 0;
  lemma_list := [];
  let (ll, extras) = to_llproof p in
  let ext = List.filter (charged_extra phrases) extras in
  let ll1 = List.fold_left discharge_extra ll ext in
  let theo = {
    LL.name = th_name;
    LL.params = [];
    LL.proof = ll1;
  } in
  List.rev (theo :: !lemma_list)
;;
