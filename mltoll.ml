(*  Copyright 2004 INRIA  *)
Misc.version "$Id: mltoll.ml,v 1.2 2004-04-08 22:51:45 doligez Exp $";;

open Expr;;
open Mlproof;;
open Printf;;

let lemma_num = ref 0;;
let lemma_list = ref [];;

let lemma_name n = sprintf "lemma_%d" n;;

let make_tau_name p = sprintf "_T_%d" (Index.get_number p);;
let make_any_name p = sprintf "_Z_%d" (Index.get_number p);;

let rec tr_term t =
  match t with
  | Evar (v, _) -> t
  | Emeta (e, _) -> evar (make_any_name e)
  | Eapp (s, es, _) -> t
  | Etau _ -> evar (make_tau_name t)
  | _ -> assert false
;;

let rec tr_prop = function
  | Evar (v, _) -> eapp (v, [])
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

let rec find_partial p partials =
  match partials with
  | [] -> raise Not_found
  | (e2, x) :: t -> if Expr.equal e2 p then x else find_partial p t
;;

let tr_rule partials r =
  match r with
  | Close1 (e) -> Llproof.Rnoteq (tr_term e)
  | Close2 (p) -> Llproof.Raxiom (tr_prop p)
  | False -> Llproof.Rfalse
  | NotTrue -> Llproof.Rnottrue
  | NotNot (p) -> Llproof.Rnotnot (tr_prop p)
  | And (p, q) -> Llproof.Rconnect (Llproof.And, tr_prop p, tr_prop q)
  | NotOr (p, q) -> Llproof.Rnotconnect (Llproof.Or, tr_prop p, tr_prop q)
  | NotImpl (p, q) -> Llproof.Rnotconnect (Llproof.Imply, tr_prop p, tr_prop q)
  | NotAll (Enot (Eall (v, t, p, _) as pp, _)) ->
      Llproof.Rnotall (tr_prop pp, make_tau_name (etau (v, t, enot (p))))
  | NotAll _ -> assert false
  | Ex (Eex (v, t, p, _) as pp) ->
      Llproof.Rex (tr_prop pp, make_tau_name (etau (v, t, p)))
  | Ex _ -> assert false
  | All (p, t) ->
      begin try
        let (p1, v, f) = find_partial p partials in
        let t1 = Expr.substitute [(v, t)] f in
        Llproof.Rall (tr_prop p1, tr_term t1)
      with Not_found -> Llproof.Rall (tr_prop p, tr_term t)
      end
  | NotEx (Enot (p, _) as e2, t) ->
      begin try
        let (e1, v, f) = find_partial e2 partials in
        let t1 = Expr.substitute [(v, t)] f in
        match e1 with
        | Enot (p1, _) -> Llproof.Rnotex (tr_prop p1, tr_term t1)
        | _ -> assert false
      with Not_found -> Llproof.Rnotex (tr_prop p, tr_term t)
      end
  | NotEx _ -> assert false
  | Or (p, q) -> Llproof.Rconnect (Llproof.Or, tr_prop p, tr_prop q)
  | Impl (p, q) -> Llproof.Rconnect (Llproof.Imply, tr_prop p, tr_prop q)
  | NotAnd (p, q) -> Llproof.Rnotconnect (Llproof.And, tr_prop p, tr_prop q)
  | Equiv (p, q) -> Llproof.Rconnect (Llproof.Equiv, tr_prop p, tr_prop q)
  | NotEquiv (p, q) -> Llproof.Rnotconnect (Llproof.Equiv, tr_prop p, tr_prop q)
  | Equal_NotEqual (e0, e1, e2, e3) ->
      Llproof.Requalnotequal (tr_term e0, tr_term e1, tr_term e2, tr_term e3)
  | P_NotP (p, q) -> Llproof.Rpnotp (tr_prop p, tr_prop q)
  | NotEqual (e1, e2) -> Llproof.Rnotequal (tr_term e1, tr_term e2)

  | Definition _ -> Llproof.Rdefinition

  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | CloseEq _
  | Ext _
    -> assert false
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

let lemma_tbl = (Hashtbl.create 997 : (string, Llproof.lemma) Hashtbl.t);;

let get_lemma p =
  let name = lemma_name (-p.mlrefc) in
  let lemma = Hashtbl.find lemma_tbl name in
  let args = List.map fst lemma.Llproof.params in
  {
    Llproof.conc = List.map tr_prop p.mlconc;
    Llproof.rule = Llproof.Rlemma (lemma.Llproof.name, args);
    Llproof.hyps = [];
  }
;;

let make_lemma llprf mlprf =
  incr lemma_num;
  let name = (lemma_name !lemma_num) in
  let refcount = mlprf.mlrefc in
  mlprf.mlrefc <- - !lemma_num;
  let l = {
    Llproof.name = name;
    Llproof.params = List.fold_left get_params [] mlprf.mlconc;
    Llproof.proof = llprf;
  } in
  Hashtbl.add lemma_tbl name l;
  lemma_list := l :: !lemma_list;
;;

let is_derived = function
  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | CloseEq _
  | Ext _
    -> true
  | _ -> false
;;

module LL = Llproof;;

let rec remove f l =
  match l with
  | [] -> []
  | h::t -> if f = h then remove f t else h::(remove f t)
;;

let rec union l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | h::t, l2 -> if List.mem h l2 then union t l2 else h::(union t l2)
;;

let rec recomp_conj sub f =
  match f with
  | Eand (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let n1 = recomp_conj sub a in
      let n2 = recomp_conj n1 b in
      {
        LL.conc = tr_prop f :: remove la (remove lb n2.LL.conc);
        LL.rule = LL.Rconnect (LL.And, la, lb);
        LL.hyps = [n2];
      }
  | Enot (a, _) -> recomp_conj_n sub a
  | _ -> sub

and recomp_conj_n sub f =
  match f with
  | Eor (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let n1 = recomp_conj_n sub a in
      let n2 = recomp_conj_n n1 b in
      {
        LL.conc = enot (tr_prop f) :: remove (enot la)
                                             (remove (enot lb) n2.LL.conc);
        LL.rule = LL.Rnotconnect (LL.Or, la, lb);
        LL.hyps = [n2];
      }
  | Eimply (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let n1 = recomp_conj sub a in
      let n2 = recomp_conj_n n1 b in
      {
        LL.conc = enot (tr_prop f) :: remove la (remove (enot lb)
                                                          n2.LL.conc);
        LL.rule = LL.Rnotconnect (LL.Imply, la, lb);
        LL.hyps = [n2];
      }
  | Enot (a, _) ->
      let la = tr_prop a in
      let n1 = recomp_conj sub a in
      {
        LL.conc = enot (tr_prop f) :: remove la n1.LL.conc;
        LL.rule = LL.Rnotnot (la);
        LL.hyps = [n1];
      }
  | _ -> sub
;;

let rec recomp_disj sub f =
  match f with
  | Eor (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, sub1) = recomp_disj sub a in
      let c1 = remove la n1.LL.conc in
      let (n2, sub2) = recomp_disj sub1 b in
      let c2 = remove lb n2.LL.conc in
      let nn = {
          LL.conc = tr_prop f :: (union c1 c2);
          LL.rule = LL.Rconnect (LL.Or, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, sub2)
  | Eimply (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, sub1) = recomp_disj_n sub a in
      let c1 = remove (enot la) n1.LL.conc in
      let (n2, sub2) = recomp_disj sub1 b in
      let c2 = remove lb n2.LL.conc in
      let nn = {
          LL.conc = tr_prop f :: (union c1 c2);
          LL.rule = LL.Rconnect (LL.Imply, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, sub2)
  | Enot (a, _) -> recomp_disj_n sub a
  | _ ->
     begin match sub with
     | h::t -> (h, t)
     | [] -> assert false
     end

and recomp_disj_n sub f =
  match f with
  | Eand (a, b, _) ->
      let la = tr_prop a and lb = tr_prop b in
      let (n1, sub1) = recomp_disj_n sub a in
      let c1 = remove (enot la) n1.LL.conc in
      let (n2, sub2) = recomp_disj_n sub b in
      let c2 = remove (enot lb) n2.LL.conc in
      let nn = {
          LL.conc = enot (tr_prop f) :: (union c1 c2);
          LL.rule = LL.Rnotconnect (LL.And, la, lb);
          LL.hyps = [n1; n2];
        }
      in (nn, sub2)
  | Enot (a, _) ->
      let la = tr_prop a in
      let (n1, sub1) = recomp_disj sub a in
      let c1 = remove la n1.LL.conc in
      let nn = {
          LL.conc = enot (tr_prop f) :: c1;
          LL.rule = LL.Rnotnot (la);
          LL.hyps = [n1];
        }
      in (nn, sub1)
  | _ ->
     begin match sub with
     | h::t -> (h, t)
     | [] -> assert false
     end
;;

exception Found of Expr.expr;;

let rec xfind_occ v e1 e2 =
  match e1, e2 with
  | Evar (v1, _), _ when v1 = v -> raise (Found e2)
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
  | Eall (v1, _, _, _), _ when v1 = v -> ()
  | Eall (_, _, f1, _), Eall (_, _, f2, _) -> xfind_occ v f1 f2
  | Eex (v1, _, _, _), _ when v1 = v -> ()
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
  | Eall (v1, _, f1, _), Eall (v2, _, f2, _) ->
     (v2, find_occ v1 f1 f2)
  | Enot (Eex (v1, _, f1, _), _), Enot (Eex (v2, _, f2, _), _) ->
     (v2, find_occ v1 f1 f2)
  | _, _ -> assert false
;;

let rec remove_partials partials l =
  match partials with
  | [] -> l
  | (e, _) :: t -> remove_partials t (remove e l)
;;

let rec to_llproof partials p =
  if p.mlrefc < 0 then
    get_lemma p
  else begin
    let result =
      if is_derived p.mlrule
      then translate_derived partials p
      else {
        LL.conc = List.map tr_prop (remove_partials partials p.mlconc);
        LL.rule = tr_rule partials p.mlrule;
        LL.hyps = List.map (to_llproof partials) (Array.to_list p.mlhyps);
      }
    in
    if p.mlrefc > 1 then begin
      make_lemma result p;
      get_lemma p
    end else begin
      result
    end
  end

and translate_derived partials p =
  match p.mlrule with
  | ConjTree (e) ->
      assert (Array.length p.mlhyps = 1);
      let sub = to_llproof partials p.mlhyps.(0) in
      recomp_conj sub e
  | DisjTree (e) ->
      let sub = List.map (to_llproof partials) (Array.to_list p.mlhyps) in
      fst (recomp_disj sub e)
  | AllPartial (e1, e2) ->
      assert (Array.length p.mlhyps = 1);
      let (x, f) = find_subst e1 e2 in
      to_llproof ((e2, (e1, x, f)) :: partials) p.mlhyps.(0)
  | NotExPartial (e1, e2) ->
      assert (Array.length p.mlhyps = 1);
      let (x, f) = find_subst e1 e2 in
      to_llproof ((e2, (e1, x, f)) :: partials) p.mlhyps.(0)
  | CloseEq (e1, e2) ->
      let f1 = tr_term e1 and f2 = tr_term e2 in
      let n1 = {
          LL.conc = [enot (eapp ("=", [f2; f2]))];
          LL.rule = LL.Rnoteq (f2);
          LL.hyps = [];
        }
      in
      let n2 = {
          LL.conc = [enot (eapp ("=", [f1; f1]))];
          LL.rule = LL.Rnoteq (f1);
          LL.hyps = [];
        }
      in
      {
        LL.conc = [eapp ("=", [f1; f2]); enot (eapp ("=", [f2; f1]))];
        LL.rule = LL.Requalnotequal (f1, f2, f2, f1);
        LL.hyps = [n1; n2];
      }
  | Ext _ ->
      let sub = Array.map (to_llproof partials) p.mlhyps in
      
      assert false (* FIXME TODO *)
  | _ -> assert false
;;

let translate p =
  lemma_num := 0;
  lemma_list := [];
  let ll = to_llproof [] p in
  let theo = {
    Llproof.name = "theorem";
    Llproof.params = [];
    Llproof.proof = ll;
  } in
  List.rev (theo :: !lemma_list)
;;
