(*  Copyright 2004 INRIA  *)
Version.add "$Id: mltoll.ml,v 1.27 2007-08-02 12:16:56 doligez Exp $";;

open Expr;;
open Misc;;
open Mlproof;;
open Namespace;;
open Printf;;

module LL = Llproof;;

let lemma_num = ref 0;;
let lemma_suffix = ref "";;
let lemma_list = ref [];;

let lemma_name n = sprintf "%s%d_%s" lemma_prefix n !lemma_suffix;;

module HE = Hashtbl.Make (Expr);;

let get_type m =
  match m with
  | Eall (v, t, e, _)
  | Eex (v, t, e, _)
     -> t
  | _ -> assert false
;;

let type_to_ident s =
  let rec newlen i n =
    if i >= String.length s then n
    else if Misc.isalnum s.[i] then newlen (i+1) (n+1)
    else newlen (i+1) (n+3)
  in
  let result = String.create (newlen 0 0) in
  let rec loop i j =
    if i >= String.length s then ()
    else if Misc.isalnum s.[i] then (result.[j] <- s.[i]; loop (i+1) (j+1))
    else begin
      let ss = sprintf "_%02x" (Char.code s.[i]) in
      String.blit ss 0 result j 3;
      loop (i+1) (j+3)
    end
  in
  loop 0 0;
  result
;;

let ident_to_type s =
  let rec newlen i n =
    if i >= String.length s then n
    else if s.[i] <> '_' then newlen (i+1) (n+1)
    else newlen (i+3) (n+1)
  in
  let result = String.create (newlen 0 0) in
  let rec loop i j =
    if i >= String.length s then ()
    else if s.[i] <> '_' then (result.[j] <- s.[i]; loop (i+1) (j+1))
    else begin
      result.[j] <- Char.chr (int_of_string ("0x" ^ String.sub s (i+1) 2));
      loop (i+3) (j+1)
    end
  in
  loop 0 0;
  result
;;

let make_meta_name e =
  sprintf "%s%d_%s" meta_prefix (Index.get_number e)
          (type_to_ident (get_type e))
;;
let is_meta s =
  String.length s >= String.length meta_prefix
  && String.sub s 0 (String.length meta_prefix) = meta_prefix
;;
let get_meta_type s =
  let len = String.length s in
  assert (len > String.length meta_prefix);
  let rec skip_digits i =
    match s.[i] with
    | '0'..'9' -> skip_digits (i+1)
    | _ -> i
  in
  let ofs = 1 + skip_digits (String.length meta_prefix) in
  ident_to_type (String.sub s ofs (len - ofs))
;;

let make_tau_name p = sprintf "%s%d" tau_prefix (Index.get_number p);;

let term_tbl = HE.create 9997;;

let memo tbl f x =
  try HE.find tbl x
  with Not_found ->
    let result = f x in
    HE.add tbl x result;
    result
;;

let rec xtr_term t =
  match t with
  | Evar (v, _) -> t
  | Emeta (e, _) -> evar (make_meta_name e)
  | Eapp (s, es, _) -> eapp (s, List.map tr_term es)
  | Etau _ -> evar (make_tau_name t)
  | Elam (v, ty, e1, _) -> elam (v, ty, tr_term e1)
  | _ -> assert false

and tr_term t = memo term_tbl xtr_term t
;;

let prop_tbl = HE.create 9997;;

let rec xtr_prop a =
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

  | Etau _ -> evar (make_tau_name a)
  | Elam _ -> assert false

and tr_prop a = memo prop_tbl xtr_prop a
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
  | NotEx (Enot (p, _), t) -> LL.Rnotex (tr_prop p, tr_term t)
  | NotEx _ -> assert false
  | Or (p, q) -> LL.Rconnect (LL.Or, tr_prop p, tr_prop q)
  | Impl (p, q) -> LL.Rconnect (LL.Imply, tr_prop p, tr_prop q)
  | NotAnd (p, q) -> LL.Rnotconnect (LL.And, tr_prop p, tr_prop q)
  | Equiv (p, q) -> LL.Rconnect (LL.Equiv, tr_prop p, tr_prop q)
  | NotEquiv (p, q) -> LL.Rnotconnect (LL.Equiv, tr_prop p, tr_prop q)
  | P_NotP (p, q) -> LL.Rpnotp (tr_prop p, tr_prop q)
  | NotEqual (e1, e2) -> LL.Rnotequal (tr_term e1, tr_term e2)

  | Definition (DefReal (sym, args, body), folded, unfolded) ->
      LL.Rdefinition (sym, tr_prop folded, tr_prop unfolded)

  | Cut (p) -> LL.Rcut (tr_prop p)

  (* derived rules, handled by translate_derived: *)
  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | Ext _
  | Close_sym _
  | Refl _
  | P_NotP_sym _
  | Trans _
  | Trans_sym _
  | TransEq _
  | TransEq_sym _
  | Definition (DefPseudo _, _, _)
    -> assert false

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
  | Emeta (m, _) -> merge [(make_meta_name m, get_type m)] accu
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
  | Elam (v, t, e, _) -> get_params accu e
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
  let name = lemma_name !lemma_num in
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
  | Close _ -> false

  | Close_refl ("=", _) -> false
  | Close_refl (_, _) -> true

  | Close_sym _ -> true

  | False | NotTrue
  | NotNot _ | And _ | NotOr _ | NotImpl _
  | NotAll _ | Ex _ | All _ | NotEx _
  | Or _ | Impl _ | NotAnd _ | Equiv _ | NotEquiv _
    -> false

  | P_NotP _ -> false

  | P_NotP_sym _ -> true

  | NotEqual _ -> false

  | Definition (DefReal _, _, _) -> false
  | Definition (DefPseudo _, _, _) -> true

  | ConjTree _
  | DisjTree _
  | AllPartial _
  | NotExPartial _
  | Refl _
  | Trans _ | Trans_sym _ | TransEq _ | TransEq_sym _
    -> true

  | Cut _ -> false
  | Ext _ -> true
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
  | Elam _, _ -> ()
  | _, _ -> assert false
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
  | (v, m) :: rest ->
      let act =
        if List.mem_assoc v rest then emeta (m) else
        begin try List.assoc v env
        with Not_found -> emeta (m)
        end
      in
      act :: (get_actuals env rest)
;;

let rec find_diff f1 f2 =
  match f1, f2 with
  | Enot (g1, _), Enot (g2, _) -> find_diff g1 g2
  | Eapp (s1, args1, _), Eapp (s2, args2, _) when s1 = s2 ->
      find_diff_list args1 args2
  | Eapp (s1, args1, _), _ -> args1
  | Evar _, _ -> []
  | _ -> assert false

and find_diff_list l1 l2 =
  match l1, l2 with
  | h1::t1, h2::t2 when Expr.equal h1 h2 -> find_diff_list t1 t2
  | h1::t1, h2::t2 ->
      assert (List.for_all2 Expr.equal t1 t2);
      find_diff h1 h2
  | _, _ -> assert false
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

let rec make_alls e vs n0 =
  match e, vs with
  | _, [] -> n0
  | Eall (v, _, body, _), h::t ->
      make_all e h (make_alls (substitute [(v, h)] body) t n0)
  | _, _ -> assert false
;;

let rec make_impls hyps con nhyps ncon =
  match hyps, nhyps with
  | [], [] -> con, ncon
  | e0::et, n0::nt ->
      let (ee, nn) = make_impls et con nt ncon in
      (eimply (e0, ee), make_impl e0 ee n0 nn)
  | _, _ -> assert false
;;

let make_direct_trans r a b c n0 =
  (* apply the transitivity hypothesis: rab rbc / rac / (n0) *)
  let trans_hyp = Eqrel.get_trans_hyp r in
  let rab = eapp (r, [a; b]) in
  let rbc = eapp (r, [b; c]) in
  let rac = eapp (r, [a; c]) in
  let n1 = make_cl rab in
  let n2 = make_cl rbc in
  let (_, n3) = make_impls [rab; rbc] rac [n1; n2] n0 in
  let n4 = make_alls trans_hyp [a; b; c] n3 in
  n4
;;

let make_direct_nsym r a b n0 =
  (* apply the symmetry hypothesis: -rab / -rba / (n0) *)
  let sym_hyp = Eqrel.get_sym_hyp r in
  let rab = eapp (r, [a; b]) in
  let rba = eapp (r, [b; a]) in
  let n1 = make_cl rab in
  let n2 = make_impl rba rab n0 n1 in
  let n3 = make_alls sym_hyp [b; a] n2 in
  n3
;;

let make_direct_sym_neq a b n0 =
  (* apply symmetry of inequality: a!=b / b!=a / (n0) *)
  let beb = eapp ("=", [b; b]) in
  let naeb = enot (eapp ("=", [a; b])) in
  let n1 = make_clr "=" b in
  let n2 = make_pnp beb naeb [n0; n1] in
  let n3 = n1 in
  let n4 = make_cut beb n2 n3 in
  n4
;;

let make_direct_sym_eq a b n0 =
  (* apply symmetry of equality: a=b / b=a / (n0) *)
  let aeb = eapp ("=", [a; b]) in
  let bea = eapp ("=", [b; a]) in
  let n1 = make_cl aeb in
  let n2 = make_direct_sym_neq b a n1 in
  let n3 = make_cut bea n0 n2 in
  n3
;;

let gethyps1 p =
  match p.mlhyps with
  | [| n1 |] -> n1
  | _ -> assert false
;;

let gethyps2 p =
  match p.mlhyps with
  | [| n1; n2 |] -> (n1, n2)
  | _ -> assert false
;;

let gethyps3 p =
  match p.mlhyps with
  | [| n1; n2; n3 |] -> (n1, n2, n3)
  | _ -> assert false
;;

let expand_trans r a b c d n1 n2 =
  let cea = eapp ("=", [c; a]) in
  let ncea = enot (cea) in
  let rca = eapp (r, [c; a]) in
  let nrca = enot (rca) in
  let bed = eapp ("=", [b; d]) in
  let rcb = eapp (r, [c; b]) in
  let rcd = eapp (r, [c; d]) in
  let nrcd = enot (rcd) in
  let rab = eapp (r, [a; b]) in
  let rad = eapp (r, [a; d]) in
  let rbd = eapp (r, [b; d]) in
  let ncea_nrca = eand (ncea, nrca) in
  let n3 = make_and ncea nrca n1 in
  let n4a = make_cl cea in
  let n4b = make_direct_sym_neq a c n4a in
  let n4c = make_nn cea n4b in
  let n5 = make_clr "=" c in
  let n6 = make_cl bed in
  let n7 = make_pnp rcb nrcd [n5; n6] in
  let n8 = make_direct_trans r c a b n7 in
  let n9 = make_nn rca n8 in
  let n10 = make_nand ncea nrca n4c n9 in
  let n11 = n6 in
  let n12 = make_pnp rab nrcd [n10; n11] in
  let n13 = make_cls "=" c a in
  let n14 = make_nn cea n13 in
  let n15 = make_cl rcd in
  let n16 = make_direct_trans r c a d n15 in
  let n17 = make_nn rca n16 in
  let n18 = make_nand ncea nrca n14 n17 in
  let n19 = make_clr "=" d in
  let n20 = make_pnp rad nrcd [n18; n19] in
  let n21 = make_direct_trans r a b d n20 in
  let n22 = make_cut rbd n21 n2 in
  let n23 = make_cut bed n12 n22 in
  let n24 = make_cut ncea_nrca n3 n23 in
  n24
;;

let expand_trans_sym r a b c d n1 n2 =
  let n3 = expand_trans r a b d c n1 n2 in
  let n4 = make_direct_nsym r c d n3 in
  n4
;;

let expand_transeq r a b c d n1 n2 n3 =
  let rcd = eapp (r, [c; d]) in
  let rbd = eapp (r, [b; d]) in
  let rcb = eapp (r, [c; b]) in
  let rca = eapp (r, [c; a]) in
  let rad = eapp (r, [a; d]) in
  let nrcd = enot (rcd) in
  let nrcb = enot (rcb) in
  let nrad = enot (rad) in
  let aeb = eapp ("=", [a; b]) in
  let n4 = make_clr "=" c in
  let n5 = make_cl rcd in
  let n6 = make_direct_trans r c b d n5 in
  let n7 = make_cut rbd n6 n3 in
  let n8 = make_pnp rcb nrcd [n4; n7] in
  let n9 = n4 in
  let n10 = make_cl aeb in
  let n11 = make_pnp rca nrcb [n9; n10] in
  let n12 = make_cut rcb n8 n11 in
  let n13 = make_direct_sym_neq a c n1 in
  let n14 = make_clr "=" d in
  let n15 = make_pnp rad nrcd [n13; n14] in
  let n16 = n10 in
  let n17 = make_direct_sym_neq b a n16 in
  let n18 = n14 in
  let n19 = make_pnp rbd nrad [n17; n18] in
  let n20 = make_cut rad n15 n19 in
  let n21 = make_cut rbd n20 n2 in
  let n22 = make_cut rca n12 n21 in
  n22
;;

let expand_transeq_sym r a b c d n1 n2 n3 =
  let n4 = expand_transeq r b a c d n1 n2 n3 in
  let n5 = make_direct_sym_eq a b n4 in
  n5
;;

let expand_trans_equal a b c d n1 n2 =
  let aeb = eapp ("=", [a; b]) in
  let nced = enot (eapp ("=", [c; d])) in
  let n3 = make_direct_sym_neq a c n1 in
  let n4 = make_pnp aeb nced [n3; n2] in
  n4
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
      let n1 = gethyps1 p in
      let vs = make_vars arity in
      let sxyz = eapp (f, vs) in
      let axyz = all_list vs (substitute [(v1, sxyz)] q) in
      let naxyz = enot (axyz) in
      let n2 = decompose_forall e1 v1 q naxyz arity f [] in
      let n3 = make_cut axyz n1 n2 in
      to_llproof n3
  | AllPartial _ -> assert false
  | NotExPartial ((Enot (Eex (v1, t1, q, _), _) as ne1), f, arity) ->
      let n1 = gethyps1 p in
      let vs = make_vars arity in
      let sxyz = eapp (f, vs) in
      let exyz = ex_list vs (substitute [(v1, sxyz)] q) in
      let n2 = decompose_exists ne1 v1 q exyz arity f [] in
      let n3 = make_cut exyz n2 n1 in
      to_llproof n3
  | NotExPartial _ -> assert false
  | Close_sym ("=", a, b) ->
      let aeb = eapp ("=", [a; b]) in
      let n1 = make_cl aeb in
      let n2 = make_direct_sym_neq b a n1 in
      to_llproof n2
  | Close_sym (s, a, b) ->
      let sym_hyp = Eqrel.get_sym_hyp s in
      let pab = eapp (s, [a; b]) in
      let pba = eapp (s, [b; a]) in
      let n1 = make_cl pab in
      let n2 = make_cl pba in
      let n3 = make_impl pab pba n1 n2 in
      let n4 = make_alls sym_hyp [a; b] n3 in
      let (n, ext) = to_llproof n4 in
      (n, union [sym_hyp] ext)
  | Close_refl ("=", _) -> assert false
  | Close_refl (s, a) ->
      let refl_hyp = Eqrel.get_refl_hyp s in
      let paa = eapp (s, [a; a]) in
      let n1 = make_cl paa in
      let n2 = make_all refl_hyp a n1 in
      let (n, ext) = to_llproof n2 in
      (n, union [refl_hyp] ext)
  | P_NotP_sym ("=", (Eapp ("=", [a; b], _) as aeb),
                     Enot (Eapp ("=", [c; d], _), _)) ->
      let (n1, n2) = gethyps2 p in
      let ndec = enot (eapp ("=", [d; c])) in
      let n3 = make_pnp aeb ndec [n1; n2] in
      let n4 = make_direct_sym_neq c d n3 in
      to_llproof n4
  | P_NotP_sym (s, (Eapp (s1, [a; b], _) as pab),
                (Enot (Eapp (s2, [c; d], _), _) as npcd)) ->
      assert (s = s1 && s = s2);
      let (n1, n2) = gethyps2 p in
      let sym_hyp = Eqrel.get_sym_hyp s in
      let pba = eapp (s, [b; a]) in
      let n3 = make_pnp pba npcd [n1; n2] in
      let n4 = make_cl pab in
      let n5 = make_impl pab pba n4 n3 in
      let n6 = make_alls sym_hyp [a; b] n5 in
      let (n, ext) = to_llproof n6 in
      (n, union [sym_hyp] ext)
  | P_NotP_sym _ -> assert false
  | Refl (s, a, b) ->
      let n1 = gethyps1 p in
      let refl_hyp = Eqrel.get_refl_hyp s in
      let paa = eapp (s, [a; a]) in
      let npab = enot (eapp (s, [a; b])) in
      let n2 = make_clr s a in
      let n3 = make_pnp paa npab [n2; n1] in
      let n4 = make_all refl_hyp a n3 in
      let (n, ext) = to_llproof n4 in
      (n, union [refl_hyp] ext)
  | Trans (Eapp ("=", [a; b], _), Enot (Eapp ("=", [c; d], _), _)) ->
      let (n1, n2) = gethyps2 p in
      let n3 = expand_trans_equal a b c d n1 n2 in
      to_llproof n3
  | Trans_sym (Eapp ("=", [a; b], _), Enot (Eapp ("=", [c; d], _), _)) ->
      let (n1, n2) = gethyps2 p in
      let n3 = expand_trans_equal a b d c n1 n2 in
      let n4 = make_direct_sym_neq c d n3 in
      to_llproof n4
  | TransEq (a, b, Enot (Eapp ("=", [c; d], _), _)) ->
      let (n1, n2, n3) = gethyps3 p in
      let n4 = expand_trans_equal a b c d n1 n3 in
      to_llproof n4
  | TransEq_sym (a, b, Enot (Eapp ("=", [c; d], _), _)) ->
      let (n1, n2, n3) = gethyps3 p in
      let n4 = expand_trans_equal a b d c n1 n3 in
      let n5 = make_direct_sym_neq c d n4 in
      to_llproof n5
  | Trans (Eapp (s1, [a; b], _), Enot (Eapp (s2, [c; d], _), _)) ->
      assert (s1 = s2);
      let (n1, n2) = gethyps2 p in
      let n3 = expand_trans s1 a b c d n1 n2 in
      let (n, ext) = to_llproof n3 in
      (n, union [Eqrel.get_trans_hyp s1] ext)
  | Trans_sym (Eapp (s1, [a; b], _), Enot (Eapp (s2, [c; d], _), _)) ->
      assert (s1 = s2);
      let (n1, n2) = gethyps2 p in
      let n3 = expand_trans_sym s1 a b c d n1 n2 in
      let (n, ext) = to_llproof n3 in
      (n, union [Eqrel.get_trans_hyp s1; Eqrel.get_sym_hyp s1] ext)
  | TransEq (a, b, Enot (Eapp (s, [c; d], _), _)) ->
      let (n1, n2, n3) = gethyps3 p in
      let n4 = expand_transeq s a b c d n1 n2 n3 in
      let (n, ext) = to_llproof n4 in
      (n, union [Eqrel.get_trans_hyp s] ext)
  | TransEq_sym (a, b, Enot (Eapp (s, [c; d], _), _)) ->
      let (n1, n2, n3) = gethyps3 p in
      let n4 = expand_transeq_sym s a b c d n1 n2 n3 in
      let (n, ext) = to_llproof n4 in
      (n, union [Eqrel.get_trans_hyp s] ext)
  | Trans _ | Trans_sym _ | TransEq _ | TransEq_sym _ -> assert false
  | Ext _ ->
      let sub = Array.map to_llproof p.mlhyps in
      Extension.to_llproof tr_prop tr_term p sub

  | Close _
  | False | NotTrue
  | NotNot _ | And _ | NotOr _ | NotImpl _
  | NotAll _ | Ex _ | All _ | NotEx _
  | Or _ | Impl _ | NotAnd _ | Equiv _ | NotEquiv _
  | P_NotP _
  | NotEqual _
  | Definition (DefReal _, _, _)
  | Cut _
    -> assert false

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
        make_node [def_hyp] (Equiv (a, b)) [[nunf]; [q]] [n1; n2]
      else
        make_node [def_hyp] (Equiv (a, b)) [[nq]; [unf]] [n2; n1]
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
      let (x, y) = if cross1 then (body, f) else (f, body) in
      let nfeb = enot (eapp ("=", [x; y])) in
      let rule2 = if sym then Close_sym ("=", y, x) else Close def_hyp in
      let n2 = make_node [nfeb; def_hyp] rule2 [] [] in
      let hyps_subs4 =
        let f f1 u1 =
          if Expr.equal f1 u1 then begin
            let neee = enot (eapp ("=", [f1; f1])) in
            ([neee], make_node [neee] (Close_refl ("=", f1)) [] [])
          end else
            ([nfeb], n2)
        in
        match folded, unfolded with
        | Eapp (_, args1, _), Eapp (_, args2, _)
        | Enot (Eapp (_, args1, _), _), Enot (Eapp (_, args2, _), _)
          -> List.map2 f args1 args2
        | _ -> assert false
      in
      let hyps4, subs4 = List.split hyps_subs4 in
      let rule4 = if cross1 then P_NotP (baseunf, folded)
                            else P_NotP (folded, negunf)
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
  lemma_suffix := th_name;
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
