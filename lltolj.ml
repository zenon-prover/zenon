open Printf
open Expr
open Llproof
open Namespace

let new_var =
  let r = ref 0 in
  fun () ->
    let n = !r in
    incr r;
    evar (sprintf "v%d" n)

exception Found of expr

let p_debug s es =
  eprintf "%s |" s;
  List.iter
    (eprintf " %a |"
       (fun oc x -> Print.expr (Print.Chan oc) x)
    ) es;
  eprintf "\n"

let p_debug_proof s (g, c, rule) =
  eprintf "%s : gamma = |" s;
  List.iter
    (eprintf " %a |"
       (fun oc x -> Print.expr (Print.Chan oc) x)) g;
  eprintf "\n and conc = |";
  eprintf " %a |"
    (fun oc x -> Print.expr (Print.Chan oc) x) c;
  eprintf "\n"

type sequent = expr list * expr list

type lkrule =
| SCaxiom of expr
| SCfalse
| SCtrue
| SCeqref of expr
| SCeqsym of expr * expr
| SCeqprop of expr * expr
| SCeqfunc of expr * expr
| SCrweak of expr * lkproof
| SClcontr of expr * lkproof
| SCcut of expr * lkproof * lkproof
| SCland of expr * expr * lkproof
| SClor of expr * expr * lkproof * lkproof
| SClimply of expr * expr * lkproof * lkproof
| SClnot of expr * lkproof
| SClall of expr * expr * lkproof
| SClex of expr * expr * lkproof
| SCrand of expr * expr * lkproof * lkproof
| SCrorl of expr * expr * lkproof
| SCrorr of expr * expr * lkproof
| SCrimply of expr * expr * lkproof
| SCrnot of expr * lkproof
| SCrall of expr * expr * lkproof
| SCrex of expr * expr * lkproof
| SCcnot of expr * lkproof
| SCext of string * expr list * expr list * lkproof list

and lkproof =
  expr list * expr * lkrule

let ingamma e proof =
  let g, c, rule = proof in
  List.exists (equal e) g

let rec rm a list =
  match list with
  | x :: list when equal x a -> list
  | x :: list -> x :: (rm a list)
  | [] -> assert false

let scaxiom (e, g) = e :: g, e, SCaxiom e
let scfalse (g, e) = efalse :: g, e, SCfalse
let sctrue (g) = g, etrue, SCtrue
let sceqref (a, g) = g, eapp ("=", [a; a]), SCeqref (a)
let sceqsym (a, b, g) =
  eapp ("=", [a; b]) :: g, eapp ("=", [b; a]), SCeqsym (a, b)
let sceqprop (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    e1 :: g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us, e2,
    SCeqprop (e1, e2)
  | _, _ -> assert false
let sceqfunc (e1, e2, g) =
  match e1, e2 with
  | Eapp (p, ts, _), Eapp (q, us, _) when p = q ->
    g @ List.map2 (fun t u -> eapp ("=", [t; u])) ts us,
    eapp ("=", [e1; e2]), SCeqfunc (e1, e2)
  | _, _ -> assert false
let scrweak (e, proof) =
  let g, c, rule = proof in
  assert (equal c efalse);
  g, e, SCrweak (e, proof)
let sclcontr (e, proof) =
  let g, c, rule = proof in
  assert (List.mem e g);
  assert (List.mem e (rm e g));
  rm e g, c, SClcontr (e, proof)
let sccut (e, proof1, proof2) =
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  assert (List.length g2 = List.length g1 + 1);
  assert (equal c1 e);
  g1, c2, SCcut(e, proof1, proof2)
let scland (e1, e2, proof) =
  assert (ingamma e2 proof);
  let (g, c, rule) = proof in
  assert (List.mem e1 (rm e2 g));
  (eand (e1, e2)) :: rm e1 (rm e2 g), c, SCland (e1, e2, proof)
let sclor (e1, e2, proof1, proof2) =
  assert (ingamma e1 proof1);
  let (g1, c, rule1) = proof1 in
  let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);
  (eor (e1, e2)) :: rm e1 g1, c, SClor (e1, e2, proof1, proof2)
let sclimply (e1, e2, proof1, proof2) =
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  assert (List.length g2 = List.length g1 + 1);
  (eimply (e1, e2)) :: g1, c2,
  SClimply (e1, e2, proof1, proof2)
let sclnot (e, proof) =
  let (g, d, rule) = proof in
  assert (equal e d);
  (enot e) :: g, efalse, SClnot (e, proof)
let sclall (e1, t, proof) =
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    assert (ingamma (substitute [(x, t)] p) proof);
    e1 :: rm (substitute [(x, t)] p) g, c, SClall (e1, t, proof)
  | _ -> assert false
let sclex (e1, v, proof) =
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    assert (ingamma (substitute [(x, v)] p) proof);
    e1 :: rm (substitute [(x, v)] p) g, c, SClex (e1, v, proof)
  | _ -> assert false
let scrand (e1, e2, proof1, proof2) =
  let (g1, d1, rule1) = proof1 in
  let (g2, _, _) = proof2 in
  assert (List.length g2 = List.length g1);
  g1, eand (e1, e2), SCrand (e1, e2, proof1, proof2)
let scrorl (e1, e2, proof) =
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorl (e1, e2, proof)
let scrorr (e1, e2, proof) =
  let (g, d, rule) = proof in
  g, eor (e1, e2), SCrorr (e1, e2, proof)
let scrimply (e1, e2, proof) =
  assert (ingamma e1 proof);
  let (g, d, rule) = proof in
  rm e1 g, eimply (e1, e2), SCrimply (e1, e2, proof)
let scrnot (e, proof) =
  assert (ingamma e proof);
  let (g, d, rule) = proof in
  rm e g, enot e, SCrnot (e, proof)
let scrall (e1, v, proof) =
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, c, rule) = proof in
    g, e1, SCrall (e1, v, proof)
  | _ -> assert false
let screx (e1, t, proof) =
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, c, rule) = proof in
    g, e1, SCrex (e1, t, proof)
  | _ -> assert false
let sccnot (e, proof) =
  let (g, c, rule) = proof in
  assert (equal c efalse);
  assert (List.mem (enot e) g);
  rm (enot e) g, e, SCcnot (e, proof)
let scconc (g, c, rule) = c
let scext (name, args, cons, proofs) = 
  cons, efalse, SCext (name, args, cons, proofs)

let lemma_env =
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)

let distinct_terms = ref []

let hypothesis_env = ref []

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)

let new_terms = ref []

let gamma_length (g, c, rule) = List.length g

let hypsofrule lkrule =
  match lkrule with
  | SCaxiom (e) -> []
  | SCfalse -> []
  | SCtrue -> []
  | SCeqref (e) -> []
  | SCeqsym (e1, e2) -> []
  | SCeqprop (e1, e2) -> []
  | SCeqfunc (e1, e2) -> []
  | SCrweak (e, proof) -> [proof]
  | SClcontr (e, proof) -> [proof]
  | SCcut (e, proof1, proof2) -> [proof1; proof2]
  | SCland (e1, e2, proof) -> [proof]
  | SClor (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClimply (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClnot (e, proof) -> [proof]
  | SClall (e1, e2, proof) -> [proof]
  | SClex (e1, e2, proof) -> [proof]
  | SCrand (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SCrorl (e1, e2, proof) -> [proof]
  | SCrorr (e1, e2, proof) -> [proof]
  | SCrimply (e1, e2, proof) -> [proof]
  | SCrnot (e, proof) -> [proof]
  | SCrall (e1, e2, proof) -> [proof]
  | SCrex (e1, e2, proof) -> [proof]
  | SCcnot (e, proof) -> [proof]
  | SCext (_, _, _, proofs) -> proofs

let applytohyps f lkproof =
  let g, c, lkrule = lkproof in
  match lkrule with
  | SCaxiom (e) -> g, c, SCaxiom (e)
  | SCfalse -> g, c, SCfalse
  | SCtrue -> g, c, SCtrue
  | SCeqref (e) -> g, c, SCeqref (e)
  | SCeqsym (e1, e2) -> g, c, SCeqsym (e1, e2)
  | SCeqprop (e1, e2) -> g, c, SCeqprop (e1, e2)
  | SCeqfunc (e1, e2) -> g, c, SCeqfunc (e1, e2)
  | SCrweak (e, proof) -> scrweak (e, f proof)
  | SClcontr (e, proof) -> sclcontr (e, f proof)
  | SCcut (e, proof1, proof2) ->
    sccut (e, f proof1, f proof2)
  | SCland (e1, e2, proof) ->
    scland (e1, e2, f proof)
  | SClor (e1, e2, proof1, proof2) ->
    sclor (e1, e2, f proof1, f proof2)
  | SClimply (e1, e2, proof1, proof2) ->
    sclimply (e1, e2, f proof1, f proof2)
  | SClnot (e, proof) -> sclnot (e, f proof)
  | SClall (e1, e2, proof) -> sclall (e1, e2, f proof)
  | SClex (e1, e2, proof) -> sclex (e1, e2, f proof)
  | SCrand (e1, e2, proof1, proof2) ->
    scrand (e1, e2, f proof1, f proof2)
  | SCrorl (e1, e2, proof) ->
    scrorl (e1, e2, f proof)
  | SCrorr (e1, e2, proof) ->
    scrorr (e1, e2, f proof)
  | SCrimply (e1, e2, proof) ->
    scrimply (e1, e2, f proof)
  | SCrnot (e, proof) -> scrnot (e, f proof)
  | SCrall (e1, e2, proof) -> scrall (e1, e2, f proof)
  | SCrex (e1, e2, proof) -> screx (e1, e2, f proof)
  | SCcnot (e, proof) -> sccnot (e, f proof)
  | SCext (name, args, cons, proofs) -> scext (name, args, cons, List.map f proofs)

let rec xaddhyp h lkproof =
  let g, c, lkrule = lkproof in
  match lkrule with
  | SCaxiom _ | SCfalse
  | SCtrue | SCeqref _ | SCeqsym _
  | SCeqprop _ | SCeqfunc _ ->
    h :: g, c, lkrule
  | _ -> applytohyps (xaddhyp h) lkproof

and addhyp hyps lkproof =
  List.fold_left (fun pf h -> xaddhyp h pf) lkproof hyps

let rec use_defs e =
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v ->
    let (params, body) = Hashtbl.find definition_env v in
    use_defs body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    use_defs (substitute (List.combine params exprs) body)
  | Evar _ | Etrue | Efalse -> e
  | Eapp (s, args, _) ->
    eapp (s, List.map use_defs args)
  | Enot (e, _) ->
    enot (use_defs e)
  | Eand (e1, e2, _) ->
    eand (use_defs e1, use_defs e2)
  | Eor (e1, e2, _) ->
    eor (use_defs e1, use_defs e2)
  | Eimply (e1, e2, _) ->
    eimply (use_defs e1, use_defs e2)
  | Eequiv (e1, e2, _) ->
    let expr1 = use_defs e1 in
    let expr2 = use_defs e2 in
    eand (eimply (expr1, expr2), eimply (expr2, expr1))
  | Eall (x, s, e, _) ->
    eall (x, s, use_defs e)
  | Eex (x, s, e, _) ->
    eex (x, s, use_defs e)
  | Etau (x, s, e, _) ->
    let tau = etau (x, s, use_defs e) in
    if List.mem_assoc tau !new_terms
    then
      List.assoc tau !new_terms
    else
      let z = new_var () in
      new_terms := (tau, z) :: !new_terms;
      z
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta (x, _) -> assert false
(* /!\ Raised by a lot of files in SYN (SYN048+1.p, SYN049+1.p, SYN315+1.p, SYN318+1.p, ...) *)

let use_defs_rule rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq (a) -> Rnoteq (use_defs a)
  | Reqsym (a, b) -> Reqsym (use_defs a, use_defs b)
  | Rnotnot (p) -> Rnotnot (use_defs p)
  | Rconnect (b, p, q) -> Rconnect (b, use_defs p, use_defs q)
  | Rnotconnect (b, p, q) ->
    Rnotconnect (b, use_defs p, use_defs q)
  | Rex (ep, v) -> Rex (use_defs ep, use_defs v)
  | Rall (ap, t) -> Rall (use_defs ap, use_defs t)
  | Rnotex (ep, t) -> Rnotex (use_defs ep, use_defs t)
  | Rnotall (ap, v) -> Rnotall (use_defs ap, use_defs v)
  | Rpnotp (e1, e2) -> Rpnotp (use_defs e1, use_defs e2)
  | Rnotequal (e1, e2) -> Rnotequal (use_defs e1, use_defs e2)
  | Rdefinition (name, sym, args, body, recarg, c, h) ->
    assert false
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map use_defs args,
      List.map use_defs cons, List.map (List.map use_defs) hyps)
  | Rlemma (name, args) ->
    assert false
  | RcongruenceLR (p, a, b) ->
    RcongruenceLR (use_defs p, use_defs a, use_defs b)
  | RcongruenceRL (p, a, b) ->
    RcongruenceRL (use_defs p, use_defs a, use_defs b)

let rec use_defs_proof proof =
  match proof.rule with
  | Rlemma (name, args) ->
    use_defs_proof (Hashtbl.find lemma_env name)
  | Rdefinition (name, sym, args, body, recarg, c, h) ->
    begin match proof.hyps with 
    | [hyp] -> use_defs_proof hyp 
    | _ -> assert false end 
  | _ ->
    {conc = List.map use_defs proof.conc;
     hyps = List.map use_defs_proof proof.hyps;
     rule = use_defs_rule proof.rule}

let rec union lists =
  match lists with
  | [] -> [], []
  | [list] -> list, [[]]
  | [] :: lists ->
    let main, remainders = union lists in
    main, main :: remainders
  | (x :: l) :: lists ->
    let main, remainders = union (l :: lists) in
    match remainders with
    | remainder :: remainders ->
      if List.mem x main
      then
	if List.mem x remainder
	then main, (rm x remainder) :: remainders
	else main, remainder :: remainders
      else
	x :: main,
	remainder :: (List.map (fun xs -> x :: xs) remainders)
    | _ -> assert false

let sceqpropbis (e1, e2, proofs, gamma) =
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf = sceqprop (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2
	(fun (l, prf) eq proof ->
	  assert (List.mem eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf =
	     gamma_length (addhyp hyps proof) + 1);
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(e1 :: eqs, prf) eqs proofs in
    proof
  | _, _ -> assert false

let sceqfuncbis (e1, e2, proofs, gamma) =
  match e1, e2 with
  | Eapp (_, ts, _), Eapp (_, us, _) ->
    let prf = sceqfunc (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2
	(fun (l, prf) eq proof ->
	  assert (List.mem eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf =
	     gamma_length (addhyp hyps proof) + 1);
	  hyps, sccut (eq, addhyp hyps proof, prf))
	(eqs, prf) eqs proofs in
    proof
  | _, _ -> assert false

let rec hypstoadd rule =
  match rule with
  | Rfalse -> [], [efalse]
  | Rnottrue -> [], [enot etrue]
  | Raxiom (p) -> [], [p; enot p]
  | Rcut (p) -> [[p]; [enot p]], []
  | Rnoteq (a) -> [], [enot (eapp ("=", [a; a]))]
  | Reqsym (a, b) ->
    [], [eapp ("=", [a; b]); enot (eapp ("=", [b; a]))]
  | Rnotnot (p) -> [[p]], [enot (enot p)]
  | Rconnect (b, p, q) ->
    begin match b with
    | And -> [[p; q]], [eand (p, q)]
    | Or -> [[p]; [q]], [eor (p, q)]
    | Imply -> [[enot p]; [q]], [eimply (p, q)]
    | Equiv ->
      [[enot p; enot q]; [p; q]],
      [eand (eimply (p, q), eimply (q, p))]  end
  | Rnotconnect (b, p, q) ->
    begin match b with
    | And -> [[enot p]; [enot q]], [enot (eand (p, q))]
    | Or -> [[enot p; enot q]], [enot (eor (p, q))]
    | Imply -> [[p; enot q]], [enot (eimply (p, q))]
    | Equiv ->
      [[enot p; q]; [p; enot q]],
      [enot (eand (eimply (p, q), eimply (q, p)))]  end
  | Rex (ep, v) ->
    begin match ep with
    | Eex (x, ty, p, _) -> [[substitute [(x, v)] p]], [ep]
    | _ -> assert false end
  | Rall (ap, t) ->
    begin match ap with
    | Eall (x, ty, p, _) -> [[substitute [(x, t)] p]], [ap]
    | _ -> assert false end
  | Rnotex (ep, t) ->
    begin match ep with
    | Eex (x, ty, p, _) ->
      [[enot (substitute [(x, t)] p)]], [enot ep]
    | _ -> assert false end
  | Rnotall (ap, v) ->
    begin match ap with
    | Eall (x, ty, p, _) ->
      [[enot (substitute [(x, v)] p)]], [enot ap]
    | _ -> assert false end
  | Rpnotp (e1, e2) ->
    begin match e1, e2 with
    | Eapp (p, ts, _), Enot (Eapp (q, us, _), _) ->
      List.map2
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us,
      [e1; e2]
    | _ -> assert false end
  | Rnotequal (e1, e2) ->
    begin match e1, e2 with
    | Eapp (p, ts, _), Eapp (q, us, _) ->
      List.map2
	(fun x y -> [enot (eapp ("=", [x; y]))]) ts us,
      [enot (eapp ("=", [e1; e2]))]
    | _ -> assert false end
  | RcongruenceLR (p, a, b) ->
    [[apply p b]], [apply p a; eapp ("=", [a; b])]
  | RcongruenceRL (p, a, b) ->
    [[apply p b]], [apply p a; eapp ("=", [b; a])]
  | Rextension (ext, name, args, concs, hyps) ->
    hyps, concs
  | Rlemma (name, args) ->
    assert false
  | _ -> assert false (* no more Rdefinition after use_defs *)

(* ---------------------------------------------------------------*)

let rec deduce_inequality e1 e2 v1 v2 c1 c2 b1 b2 gamma proof =
  let n1 = List.assoc v1 !distinct_terms in
  let n2 = List.assoc v2 !distinct_terms in
  let eq = eapp ("=", [e1; e2]) in
  let b3 = n1 < n2 in
  let ax =
    if b3
    then eapp ("=", [v1; v2])
    else eapp ("=", [v2; v1]) in
  let rec f b1 b2 b3 =
    match b1, b2, b3 with
    | true, true, true -> sceqprop (eq, ax, [])
    | _, _, false ->
      sccut (
	eapp ("=", [v1; v2]),
	f b1 b2 true, sceqsym (v1, v2, [c1; c2; eq]))
    | _, false, _ ->
      sccut (
	eapp ("=", [e2; v2]),
	sceqsym (v2, e2, [c1; eq]), addhyp [c2] (f b1 true b3))
    | false, _, _ ->
      sccut (
	eapp ("=", [e1; v1]),
	sceqsym (v1, e1, [c2; eq]), addhyp [c1] (f true b2 b3))
  in
  sccut (
    enot eq,
    addhyp (rm (enot ax) gamma) (
      scrnot (eq, sclnot (ax, (f b1 b2 b3)))),
    addhyp [c1; c2] proof)

let rec xrmdblnot e proof =
  let g, c, rule = proof in
  match rule with
  | SCaxiom (Enot (f, _)) ->
    assert (equal f e);
    sclnot (f, scaxiom (f, rm (enot f) g))
  | SCeqprop _ | SCeqfunc _ | SCtrue | SCeqref _ | SCeqsym _
  | SCrimply _ | SCrand _ | SCrorl _ | SCrorr _
  | SCrall _ | SCrex _ -> assert false
  | SCfalse -> scfalse (e :: (rm efalse g), efalse)
  | SClnot (f, prf) -> addhyp [e] prf
  | SCrnot (f, prf) -> assert (equal f e); prf
  | _ -> assert false

let rec rmdblnot e proof =
  let g, c, rule = proof in
  match rule with
  | SClnot (Enot (f, _), prf) when equal f e ->
    xrmdblnot e prf
  | SCaxiom (Enot (Enot (f, _), _)) when equal f e ->
    scrnot (
      enot e, sclnot (e, scaxiom (e, rm (enot (enot e)) g)))
  | SCaxiom (f) -> scaxiom (f, e :: (rm f (rm (enot (enot e)) g)))
  | SCfalse -> scfalse (e :: rm (enot (enot e)) g, c)
  | SCtrue -> sctrue (e :: rm (enot (enot e)) g)
  | SCeqref (a) -> sceqref (a, e :: rm (enot (enot e)) g)
  | SCeqsym (a, b) -> sceqsym (a, b, e :: rm (enot (enot e)) g)
  | SCeqprop (a, b) -> sceqprop (a, b, e :: rm (enot (enot e)) g)
  | SCeqfunc (a, b) -> sceqfunc (a, b, e :: rm (enot (enot e)) g)
  | SClcontr (Enot (Enot (f, _), _), prf) when equal f e ->
    sclcontr (f, rmdblnot e (rmdblnot e prf))
  | SCcut (_, prf1, prf2) -> applytohyps (rmdblnot e) proof
  | _ -> applytohyps (rmdblnot e) proof

let rec clean f prf =
  let g, c, rule = prf in
  match rule with
  | SCeqsym _ | SCeqref _
  | SCtrue | SCaxiom _ | SCfalse
  | SCeqprop _ | SCeqfunc _ ->
    assert (List.mem f g);
    rm f g, c, rule
  | _ -> applytohyps (clean f) prf

and useful e proof =
  let g, c, rule = proof in
  match rule with
  | SCeqsym (a, b) ->
    equal e (eapp ("=", [a; b])) && not (List.mem e (rm e g))
  | SCeqref (a) -> false
  | SCtrue -> false
  | SCaxiom (a) -> equal e a && not (List.mem e (rm e g))
  | SCfalse -> equal e efalse && not (List.mem e (rm e g))
  | SCeqprop (Eapp (p, ts, _) as f1, Eapp (_, us, _)) ->
    let x = equal e f1 in
    List.fold_left2
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      x ts us
  | SCeqprop _ -> assert false
  | SCeqfunc (Eapp (p, ts, _), Eapp (_, us, _)) ->
    List.fold_left2
      (fun x t u -> (x || equal e (eapp ("=", [t; u]))))
      false ts us
  | SCeqfunc _ -> assert false
  | SClcontr (f, _)
      when (equal e f && not (List.mem e (rm e g))) -> true
  | SClor (a, b, _, _)
      when (equal e (eor (a, b))
	    && not (List.mem e (rm e g))) -> true
  | SCland (a, b, _)
      when (equal e (eand (a, b))
	    && not (List.mem e (rm e g))) -> true
  | SClex (f, _, _)
      when (equal e f && not (List.mem e (rm e g))) -> true
  | SClall (f, _, _)
      when (equal e f && not (List.mem e (rm e g))) -> true
  | SClnot (f, _)
      when (equal e (enot f) && not (List.mem e (rm e g))) -> true
  | SClimply (a, b, _, _)
      when (equal e (eimply (a, b))
	    && not (List.mem e (rm e g))) -> true
  | SClcontr _ | SClor _ | SCland _ | SClex _
  | SClall _ | SClnot _ | SClimply _ | SCcut _
  | SCrimply _ | SCrnot _ | SCrex _ | SCrall _
  | SCrand _ | SCrorr _ | SCrorl _ | SCrweak _ | SCcnot _
    -> List.exists (useful e) (hypsofrule rule)
  | SCext _ -> true (* à corriger ? *)

let rec lefttoright e proof =
  let g, c, rule = proof in
  let ne = enot e in
  assert (List.mem ne g);
  if not (useful ne proof)
  then scrweak (e, clean ne proof)
  else
    match e with
    | Enot (f, _) ->
      optimize (scrnot (f, rmdblnot f proof))
    | _ ->
      assert (equal c efalse);
      assert (ingamma ne proof);
      match rule with
      | SClnot (f, prf)
	  when (equal f e) -> prf
      | SClcontr (f, _)
	  when (equal ne f) -> sccnot (e, proof)
      | SClimply (a, b, prf1, prf2)
	  when (not (useful ne prf1)) ->
	sclimply (a, b, clean ne prf1, lefttoright e prf2)
      | SCcut (a, prf1, prf2)
	  when (not (useful ne prf1)) ->
	sccut (a, clean ne prf1, lefttoright e prf2)
      | SClnot _ | SCcut _ | SClimply _
      | SCext _ ->
	sccnot (e, proof)
      | SCaxiom _ | SCfalse ->
	scfalse (rm efalse (rm ne g), e)
      | SClcontr _ | SClor _ | SCland _ | SClex _ | SClall _
	-> applytohyps (lefttoright e) proof
      | SCrex _ | SCrall _ | SCrand _ | SCrorr _ | SCrorl _
      | SCrimply _ | SCrnot _ | SCeqfunc _ | SCeqprop _
      | SCeqsym _ | SCeqref _ | SCtrue | SCcnot _ | SCrweak _
	-> assert false

and righttoleft e proof =
  let g, c, rule = proof in
  let ne = enot e in
  match rule with
  | SCcnot (f, prf) -> prf
  | SClnot _ -> assert false
  | SClimply (f1, f2, prf1, prf2) ->
    sclimply (f1, f2, xaddhyp ne prf1, righttoleft e prf2)
  | SCcut (f, prf1, prf2) ->
    sccut (f, xaddhyp ne prf1, righttoleft e prf2)
  | SCland _ | SClor _ | SClall _ | SClex _
    -> applytohyps (righttoleft e) proof
  | SCaxiom _ | SCfalse | SCtrue | SCeqref _ | SCeqsym _
  | SCeqprop _ | SCeqfunc _ | SCrweak _
    -> sclnot (e, proof)
  | SCrand _ | SCrorl _ | SCrorr _
  | SCrimply _ | SCrnot _ | SCrall _ | SCrex _ | SClcontr _
  | SCext _
    -> sclnot (e, proof)

and optimize proof =
  let g, c, rule = proof in
  match rule with
  | SCcnot (e, prf) ->
    lefttoright e prf
  | SClnot (e, prf) ->
    righttoleft e prf
  | _ -> applytohyps optimize proof

let rec xrmcongruence s x t a b =
  let eq =
    if s
    then eapp ("=", [a; b])
    else eapp ("=", [b; a]) in
  match t with
  | Evar (v, _) when (equal x t) ->
    if s
    then scaxiom (eapp ("=", [a; b]), [])
    else sceqsym (b, a, [])
  | Evar _ | Etau _ -> sceqref (t, [eq])
  | Eapp (f, args, _) ->
    sceqfuncbis (
      substitute [(x, a)] t, substitute [(x, b)] t,
      List.map (fun t -> xrmcongruence s x t a b) args, [eq])
  | _ -> assert false

let rec rmcongruence s x e a b =
  let eq =
    if s
    then eapp ("=", [a; b])
    else eapp ("=", [b; a]) in
  match e with
  | Etrue | Efalse | Evar _ -> scaxiom (e, [])
  | Eapp (f, args, _) ->
    sceqpropbis (
      substitute [(x, a)] e, substitute [(x, b)] e,
      List.map (fun t -> xrmcongruence s x t a b) args, [eq])
  | Eand (e1, e2, _) ->
    scland (
      substitute [(x, a)] e1, substitute [(x, a)] e2,
      scrand (
	substitute [(x, b)] e1, substitute [(x, b)] e2,
	addhyp [substitute [(x, b)] e2] (rmcongruence s x e1 a b),
	addhyp [substitute [(x, b)] e1] (rmcongruence s x e2 a b)))
  | Eor (e1, e2, _) ->
    sclor (
      substitute [(x, a)] e1, substitute [(x, a)] e2,
      scrorl (
	substitute [(x, b)] e1, substitute [(x, b)] e2,
	rmcongruence s x e1 a b),
      scrorr (
	substitute [(x, b)] e1, substitute [(x, b)] e2,
	rmcongruence s x e2 a b))
  | Eimply (e1, e2, _) ->
    scrimply (
      substitute [(x, b)] e1, substitute [(x, b)] e2,
      sclimply (
	substitute [(x, a)] e1, substitute [(x, a)] e2,
	rmcongruence (not s) x e1 b a,
	addhyp [substitute [(x, b)] e1] (rmcongruence s x e2 a b)))
  | Enot (e0, _) ->
    scrnot (
      substitute [(x, b)] e0,
      sclnot (
	substitute [(x, a)] e0,
	rmcongruence (not s) x e0 b a))
  | Eall (y, ty, e0, _) ->
    let z = new_var () in
    scrall (
      substitute [(x, b)] e,
      substitute [(x, b)] z,
      sclall (
	substitute [(x, a)] e,
	substitute [(x, a)] z,
	rmcongruence s x
	  (substitute [(y, z)] e0) a b))
  | Eex (y, ty, e0, _) ->
    let z = new_var () in
    screx (
      substitute [(x, b)] e,
      substitute [(x, b)] z,
      sclex (
	substitute [(x, a)] e,
	substitute [(x, a)] z,
	rmcongruence s x
	  (substitute [(y, z)] e0) a b))
    | Etau _ | Elam _ | Emeta _ | Eequiv _ ->
    assert false

let rec xlltolkrule rule hyps gamma =
  match rule, hyps with
  | Rfalse, [] ->
    scfalse (gamma, efalse)
  | Rnottrue, [] ->
    righttoleft etrue (sctrue (gamma))
  | Raxiom (p), [] ->
    righttoleft p (scaxiom (p, gamma))
  | Rcut (p), [proof1; proof2] ->
    sccut (enot p, scrnot (p, proof1), proof2)
  | Rnoteq (a), [] ->
    righttoleft (eapp ("=", [a; a])) (sceqref (a, gamma));
  | Reqsym (a, b), [] ->
    righttoleft (eapp ("=", [b; a]))
      (sceqsym (a, b, gamma))
  | Rnotnot (p), [proof] ->
    righttoleft (enot (p))
      (scrnot (p, proof))
  | Rconnect (And, p, q), [proof] ->
    scland (p, q, proof)
  | Rconnect (Or, p, q), [proof1; proof2] ->
    sclor (p, q, proof1, proof2)
  | Rconnect (Imply, p, q), [proof1; proof2] ->
    assert (ingamma (enot p) proof1);
    sclimply (p, q, lefttoright p proof1, proof2)
  | Rconnect (Equiv, p, q), [proof1; proof2] ->
    assert (ingamma (enot q) proof1);
    assert (ingamma (enot p) (sclimply (
      q, p,
      lefttoright q proof1,
      righttoleft p (scaxiom (p, gamma)))));
    scland (
      eimply (p, q), eimply (q, p),
      sclimply (
	p, q,
	lefttoright p
	  (sclimply (
	    q, p,
	    lefttoright q proof1,
	    righttoleft p (scaxiom (p, gamma)))),
	sclimply (
	  q, p,
	  scaxiom (q, gamma), proof2)))
  | Rnotconnect (And, p, q), [proof1; proof2] ->
    assert (ingamma (enot p) proof1);
    assert (ingamma (enot q) proof2);
    righttoleft (eand (p, q))
      (scrand (p, q, lefttoright p proof1, lefttoright q proof2))
  | Rnotconnect (Or, p, q), [proof] ->
    assert (ingamma (enot q) proof);
    assert (ingamma (enot p)
	      (righttoleft (eor (p, q)) (
		scrorr (
		  p, q,
		  lefttoright q proof))));
    if not (useful (enot p) proof)
    then
      righttoleft (eor (p, q)) (
	scrorr (
	  p, q,
	  lefttoright q (clean (enot p) proof)))
    else if not (useful (enot q) proof)
    then
      righttoleft (eor (p, q)) (
	scrorl (
	  p, q,
	  lefttoright p (clean (enot q) proof)))
    else
    begin match q with
    | Enot _ ->
      sclcontr (
	enot (eor (p, q)),
	righttoleft (eor (p, q)) (
	  scrorr (
	    p, q,
	    lefttoright q (
	      righttoleft (eor (p, q)) (
		scrorl (
		  p, q,
		  lefttoright p proof))))))
    | _ ->
      sclcontr (
	enot (eor (p, q)),
	righttoleft (eor (p, q)) (
	  scrorl (
	    p, q,
	    lefttoright p (
	      righttoleft (eor (p, q)) (
		scrorr (
		  p, q,
		  lefttoright q proof)))))) end
  | Rnotconnect (Imply, p, q), [proof] ->
    righttoleft (eimply (p, q))
      (scrimply (p, q, lefttoright q proof))
  | Rnotconnect (Equiv, p, q), [proof1; proof2] ->
    assert (ingamma (enot q) proof2);
    assert (ingamma (enot p) proof1);
    righttoleft (eand (eimply (p, q), eimply (q, p)))
      (scrand (eimply (p, q), eimply (q, p),
	       scrimply (p, q, lefttoright q proof2),
	       scrimply (q, p, lefttoright p proof1)))
  | Rex (ep, v), [proof] ->
    sclex (ep, v, proof)
  | Rall (ap, t), [proof] ->
    sclall (ap, t, proof)
  | Rnotex (Eex(x, ty, p, _) as ep, t), [proof] ->
    assert (ingamma (enot (substitute [(x, t)] p)) proof);
    righttoleft ep
      (screx (ep, t, lefttoright (substitute [(x, t)] p) proof))
  | Rnotall (Eall(x, ty, p, _) as ap, v), [proof] ->
    assert (ingamma (enot (substitute [(x, v)] p)) proof);
    righttoleft ap (
      scrall (
	ap, v,
	lefttoright (substitute [(x, v)] p) proof))
  | Rpnotp (Eapp (_, ts, _) as e1,
	    Enot (Eapp (_, us, _) as e2, _)), proofs ->
    let prf = sceqprop (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2
	(fun (l, prf) eq proof ->
	  assert (List.mem eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf =
	     gamma_length (addhyp hyps (lefttoright eq proof)) + 1);
	  hyps, sccut (eq, addhyp hyps (lefttoright eq proof), prf))
	(e1 :: eqs, prf) eqs proofs in
    righttoleft e2 proof
  | Rnotequal (Eapp (_, ts, _) as e1,
	       (Eapp (_, us, _) as e2)), proofs ->
    let prf = sceqfunc (e1, e2, gamma) in
    let eqs = List.map2 (fun t u -> eapp ("=", [t; u])) ts us in
    let _, proof =
      List.fold_left2
	(fun (l, prf) eq proof ->
	  assert (List.mem eq l);
	  let hyps = rm eq l in
	  assert (gamma_length prf =
	     gamma_length (addhyp hyps (lefttoright eq proof)) + 1);
	  hyps, sccut (eq, addhyp hyps (lefttoright eq proof), prf))
	(eqs, prf) eqs proofs in
    righttoleft (eapp ("=", [e1; e2])) proof
  | RcongruenceLR (p, a, b), [proof] ->
    let g, c, rule = proof in
    begin match p with
    | Elam (x, ty, e, _) ->
      let prf1 =
	addhyp (rm (apply p b) g) (rmcongruence true x e a b) in
      let prf2 = addhyp [apply p a; eapp ("=", [a; b])] proof in
      assert (gamma_length prf2 =
	  gamma_length prf1 + 1);
      sccut (
	apply p b,
	addhyp (rm (apply p b) g) (rmcongruence true x e a b),
	addhyp [apply p a; eapp ("=", [a; b])] proof)
    | _ -> assert false end
  | RcongruenceLR (p, a, b), _ -> assert false
  | RcongruenceRL (p, a, b), [proof] ->
    let g, c, rule = proof in
    begin match p with
    | Elam (x, ty, e, _) ->
      let prf1 =
	addhyp (rm (apply p b) g) (rmcongruence false x e a b) in
      let prf2 = addhyp [apply p a; eapp ("=", [a; b])] proof in
      assert (gamma_length prf2 =
	  gamma_length prf1 + 1);
      sccut (
	apply p b,
	addhyp (rm (apply p b) g) (rmcongruence false x e a b),
	addhyp [apply p a; eapp ("=", [a; b])] proof)
    | _ -> assert false end
  | Rdefinition (name, sym, args, body, recarg, fld, unf), [proof]
    -> assert false
  | Rextension (
    "", "zenon_notallex", [Elam (v, t, p, _)],
    [Enot (Eall (x, s, e, _) as ap, _)], [[ep]]), [proof] ->
    let g, c, rule = proof in
    begin match rule with
    | SClex (exp, y, prf)
	when (equal exp ep) ->
      let q = substitute [(v, y)] p in
      assert (ingamma (enot q) prf);
      righttoleft ap
	(scrall (
	  ap, y, lefttoright q prf))
    | _ ->
      let z = new_var () in
      let q = substitute [(v, z)] p in
      righttoleft ap
	(scrall (
	  ap, z, lefttoright q (
	    sccut (
	      ep,
	      screx (
		ep, z, scaxiom (
		  enot q, gamma)), addhyp [enot q]  proof)))) end
  | Rextension ("", "zenon_stringequal", [s1; s2], [c], []), [] ->
    let v1 = eapp ("$string", [s1]) in
    let v2 = eapp ("$string", [s2]) in
    let n1 = List.assoc v1 !distinct_terms in
    let n2 = List.assoc v2 !distinct_terms in
    let c = eapp ("=", [v1; v2]) in
    if n1 < n2
    then righttoleft c (scaxiom (c, rm (enot c) gamma))
    else righttoleft c (sceqsym (v1, v2, rm (enot c) gamma))
  | Rextension (
    "", "zenon_stringdiffll", [e1; v1; e2; v2],
    [c1; c2], [[h]]), [proof] ->
    deduce_inequality e1 e2 v1 v2 c1 c2 true true gamma proof
  | Rextension (
    "", "zenon_stringdifflr", [e1; v1; e2; v2],
    [c1; c2], [[h]]), [proof] ->
    deduce_inequality e1 e2 v1 v2 c1 c2 true false gamma proof
  | Rextension (
    "", "zenon_stringdiffrl", [e1; v1; e2; v2],
    [c1; c2], [[h]]), [proof] ->
    deduce_inequality e1 e2 v1 v2 c1 c2 false true gamma proof
  | Rextension (
    "", "zenon_stringdiffrr", [e1; v1; e2; v2],
    [c1; c2], [[h]]), [proof] ->
    deduce_inequality e1 e2 v1 v2 c1 c2 false false gamma proof
  | Rextension (ext, name, args, cons, hyps), proofs ->
    scext(name, args, cons, proofs)
  | Rlemma _, _ -> assert false (* no lemma after use_defs *)
  | Rdefinition _, _ -> assert false (* no definition after use_defs *)
  | _ -> assert false

let rec lltolkrule proof gamma =
  let hypslist, conclist = hypstoadd proof.rule in
  let newcontr, list =
    List.fold_left (fun (cs, es) e ->
      if (List.mem e es)
      then
	cs, rm e es
      else
	e :: cs, es)
      ([], gamma) conclist in
  let contrshyps =
    List.map2 lltolkrule proof.hyps
      (List.map (List.rev_append list) hypslist) in
  let contrs, prehyps = List.split contrshyps in
  let maincontr, remainders = union contrs in
  let hyps = List.map2 addhyp remainders prehyps in
  let preproof = xlltolkrule proof.rule hyps (maincontr@list) in
  List.fold_left
    (fun (cs, prf) c ->
      if List.mem c conclist
      then cs, sclcontr (c, prf)
      else c :: cs, prf)
    (newcontr, preproof) maincontr

let rec constructive proof =
  let (g, c, rule) = proof in
  match rule with
  | SCcnot _ -> false
  | _ -> List.fold_left
    (fun b prf -> b && constructive prf) true (hypsofrule rule)

let rec lltolk proof goal =
  let pregamma =
    match goal with
    | Some (Enot (g, _)) -> enot g :: !hypothesis_env
    | None -> !hypothesis_env
    | _ -> assert false in
  let gamma = List.map use_defs pregamma in
  let l, lkproof = lltolkrule proof gamma in
  assert (l = []);
  lkproof

(* ----------------------------------------------------------- *)

let rec unify e1 e2 =
  match e1, e2 with
  | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) ->
    enot (enot (unify f1 f2))
  | Enot (Enot (f1, _), _), _ -> enot (enot (unify f1 e2))
  | _, Enot (Enot (f2, _), _) -> enot (enot (unify e1 f2))
  | Etrue, Etrue -> etrue
  | Efalse, Efalse -> efalse
  | Evar (x, _), Evar (y, _) when (x = y) -> evar (x)
  | Eapp (x, args1, _), Eapp (y, args2, _)
    when (x = y && List.for_all2 equal args1 args2) ->
    eapp (x, args1)
  | Eand (f1, f2, _), Eand (f3, f4, _) ->
    eand (unify f1 f3, unify f2 f4)
  | Eor (f1, f2, _), Eor (f3, f4, _) ->
    eor (unify f1 f3, unify f2 f4)
  | Eimply (f1, f2, _), Eimply (f3, f4, _) ->
    eimply (unify f1 f3, unify f2 f4)
  | Enot (f1, _), Enot (f2, _) -> enot (unify f1 f2)
  | Eall (x, ty1, f1, _), Eall (y, _, f2, _) ->
    eall (x, ty1, unify f1 (substitute [(y, x)] f2))
  | Eex (x, ty1, f1, _), Eex (y, _, f2, _) ->
    eex (x, ty1, unify f1 (substitute [(y, x)] f2))
  | _, _ -> p_debug "fail unify" [e1; e2]; assert false

let rec merge assocs =
  match assocs with
  | l1 :: l2 :: assocs ->
    let _,l = List.fold_left
      (fun (q, r) (a, b) ->
	List.remove_assoc a q, (a, unify b (List.assoc a q)) :: r)
      (l1, []) l2 in
    merge (l :: assocs)
  | [l] -> l;
  | _ -> assert false

let replace l1 l2 =
  let _, l = List.fold_left
    (fun (q, r) (a, b) ->
      List.remove_assoc a q, (b, List.assoc a q) :: r)
    (l1, []) l2 in l

let newcut l aplus proof1 proof2 =
  let (g1, c1, rule1) = proof1 in
  let (g2, c2, rule2) = proof2 in
  if equal aplus c1
  then
    l, sccut (aplus, proof1, proof2)
  else
    match c1 with
    | Enot (Enot (c, _), _) when equal c aplus ->
      if equal c2 efalse
      then
	l, sccut (
	  c1, proof1,
	  sclnot (enot c, scrnot (c, proof2)))
      else
	l, sccut (
	  c1, proof1,
	  scrnot (
	    enot c2, sclnot (
	      enot c, scrnot (
		c, sclnot (c2, proof2)))))
    | _ ->
      p_debug "\nfail cut" [c1; aplus];
      assert false              (* /!\ Raised by SYN919+1.p *)

let rec adaptaxiom g e1 e2 =
  match e1, e2 with
  | Etrue, Etrue | Efalse, Efalse
  | Evar _, Evar _ | Eapp _, Eapp _
    -> scaxiom (e1, g)
  | Enot (f1, _), Enot (f2, _) ->
    scrnot (
      f2, sclnot (
	f1, adaptaxiom g f2 f1))
  | Eand (f1, f2, _), Eand (f3, f4, _) ->
    scland (f1, f2, scrand (
      f3, f4,
      adaptaxiom (f2 :: g) f1 f3,
      adaptaxiom (f1 :: g) f2 f4))
  | Eor (f1, f2, _), Eor (f3, f4, _) ->
    sclor (
      f1, f2,
      scrorl (f3, f4, adaptaxiom g f1 f3),
      scrorr (f3, f4, adaptaxiom g f2 f4))
  | Eimply (f1, f2, _), Eimply (f3, f4, _) ->
   scrimply (f3, f4, sclimply (
     f1, f2,
     adaptaxiom g f3 f1,
     adaptaxiom (f3 :: g) f2 f4))
  | Eall (x, ty, f1, _), Eall (y, _, f2, _) ->
    let z = new_var () in
    scrall (
      e2, z, sclall (
	e1, z, adaptaxiom g
	  (substitute [(x, z)] f1)
	  (substitute [(y, z)] f2)))
  | Eex (x, ty, f1, _), Eex (y, _, f2, _) ->
    let z = new_var () in
    sclex (
      e1, z, screx (
	e2, z, adaptaxiom g
	  (substitute [(x, z)] f1)
	  (substitute [(y, z)] f2)))
  | _, Enot (Enot (f2, _), _) ->
    scrnot (
      enot (f2), sclnot (
	f2, adaptaxiom g e1 f2))
  | _, _ -> assert false

let rec ladapt proof (u, v) =
  if equal u v then proof else
    let g, c, rule = proof in
    let result = match rule, v with
    | SClor (a, b, proof1, proof2), Eor (sa, sb, _)
      when (equal u (eor (a, b))) ->
      sclor (sa, sb, ladapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClimply (a, b, proof1, proof2), Eimply (sa, sb, _)
      when (equal u (eimply (a, b))) ->
      sclimply (
	sa, sb, radapt proof1 (a, sa), ladapt proof2 (b, sb))
    | SClcontr (a, proof), _
      when (equal a u) ->
      sclcontr (v, ladapt (ladapt proof (a, v)) (a, v))
    | SCland (a, b, proof), Eand (sa, sb, _)
      when (equal u (eand (a, b))) ->
      scland (sa, sb, ladapt (ladapt proof (a, sa)) (b, sb))
    | SClnot (a, proof), Enot (sa, _)
      when (equal u (enot a)) ->
      sclnot (sa, radapt proof (a, sa))
    | SClall (Eall (var, ty, e, _) as ap, t, proof),
	Eall (svar, _, se, _)
	  when (equal u ap) ->
      let z = substitute [(var, t)] e in
      let sz = substitute [(svar, t)] se in
      sclall (eall (svar, ty, se), t, ladapt proof (z, sz))
    | SClex (Eex (var, ty, e, _) as ep, v, proof),
      Eex (svar, _, se, _)
	when (equal u ep) ->
      let z = substitute [(var, v)] e in
      let sz = substitute [(svar, v)] se in
      sclex (eex (svar, ty, se), v, ladapt proof (z, sz))
    | SCaxiom (a), _ when equal u a -> adaptaxiom (rm u g) v u
    | SClnot _, _ | SClimply _, _ | SClor _, _ | SCland _, _
    | SClcontr _, _ | SCcut _, _ | SClex _, _ | SClall _, _
    | SCrweak _, _ | SCrnot _, _ | SCrand _, _ | SCrimply _, _
    | SCrorl _, _ | SCrorr _, _ | SCrall _, _ | SCrex _, _
      -> applytohyps (fun proof -> ladapt proof (u, v)) proof
    | SCext _, _
    | SCeqfunc _, _ | SCeqprop _, _
    | SCaxiom _, _ | SCfalse, _
    | SCtrue, _ | SCeqref _, _
    | SCeqsym _, _ -> v :: (rm u g), c, rule
    | SCcnot _, _ -> assert false in
    let resultg, _, _ = result in
    assert (List.length resultg = List.length g);
    result

and radapt proof (a, b) =
  let rec xadapt proof (u, v) =
    let g, c, rule = proof in
    match rule, v with
    | SCcut (a, proof1, proof2), _ ->
      sccut (a, proof1, radapt proof2 (u, v))
    | SClimply (a, b, proof1, proof2), _ ->
      sclimply (a, b, proof1, radapt proof2 (u, v))
    | SCrand (a, b, proof1, proof2), Eand (xa, xb, _) ->
      scrand (xa, xb, radapt proof1 (a, xa), radapt proof2 (b, xb))
    | SCrweak (a, proof), _ -> scrweak (v, proof)
    | SClnot (a, proof), _ -> sclnot (a, proof)
    | SCrorl (a, b, proof), Eor (xa, xb, _) ->
      scrorl (xa, xb, radapt proof (a, xa))
    | SCrorr (a, b, proof), Eor (xa, xb, _) ->
      scrorr (xa, xb, radapt proof (b, xb))
    | SCrimply (a, b, proof), Eimply (xa, xb, _) ->
      scrimply (xa, xb, radapt (ladapt proof (a, xa)) (b, xb))
    | SCrnot (a, proof), Enot (xa, _) ->
      scrnot (xa, ladapt proof (a, xa))
    | SCrall (Eall (var, ty, e, _), v, proof),
      Eall (xvar, _, xe, _) ->
      let z = substitute [(var, v)] e in
      let xz = substitute [(xvar, v)] xe in
      scrall (eall (xvar, ty, xe), v, radapt proof (z, xz))
    | SCrex (Eex (var, ty, e, _), t, proof),
      Eex (xvar, _, xe, _) ->
      let z = substitute [(var, t)] e in
      let xz = substitute [(xvar, t)] xe in
      screx (eex (xvar, ty, xe), t, radapt proof (z, xz))
    | SCtrue, _ | SCeqref _, _ | SCeqsym _, _
    | SCeqfunc _, _ | SCeqprop _, _  -> proof
    | SCaxiom _, _ -> adaptaxiom (rm u g) u v
    | SCfalse, _ -> g, v, rule
    | SClcontr _, _ | SClor _, _ | SCland _, _
    | SClall _, _ | SClex _, _
      -> applytohyps (fun proof -> radapt proof (u, v)) proof
    | SCcnot _, _ -> assert false
    | _, _ -> assert false in    (* /!\ raised by CSR057+1.p *)
  let rec headnots e1 e2 =
    match e1, e2 with
    | Enot (Enot (f1, _), _), Enot (Enot (f2, _), _) ->
      headnots f1 f2
    | _, Enot (Enot (f2, _), _) -> true
    | _, _ -> false in
  if equal a b
  then proof
  else
    if headnots a b
    then
      match b with
      | Enot (Enot (e, _), _) ->
	scrnot (enot (e), sclnot (e, radapt proof (a, e)))
      | _ -> assert false;
    else
      xadapt proof (a, b)

let rec weaken ex et =
  match ex, et with
  | Enot (Enot (fx, _), _), Enot (Enot (ft, _), _) ->
    enot (enot (weaken fx ft))
  | _, Enot (Enot (ft, _), _) -> enot (enot (weaken ex ft))
  | Etrue, _ | Efalse, _
  | Evar _, _ | Eapp _, _-> ex
  | Eand (fx1, fx2, _), Eand (ft1, ft2, _) ->
    eand (weaken fx1 ft1, weaken fx2 ft2)
  | Eor (fx1, fx2, _), Eor (ft1, ft2, _) ->
    eor (weaken fx1 ft1, weaken fx2 ft2)
  | Eimply (fx1, fx2, _), Eimply (ft1, ft2, _) ->
    eimply (weaken fx1 ft1, weaken fx2 ft2)
  | Enot (fx, _), Enot (ft, _) -> enot (weaken fx ft)
  | Eall (x, tyx, fx, _), Eall (y, _, ft, _) ->
    eall (x, tyx, weaken fx (substitute [(y, x)] ft))
  | Eex (x, tyx, fx, _), Eex (y, _, ft, _) ->
    eex (x, tyx, weaken fx (substitute [(y, x)] ft))
  | _, _ -> assert false

let rec lltoljrule lkproof =
  let lkg, lkc, rule = lkproof in
  let assocs, proofs =
    List.split (List.map lltoljrule (hypsofrule rule)) in
  let ljlist, ljprf =
  match rule, assocs, proofs with
    | SCcut (a, lklkprf1, lklkprf2), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; List.remove_assoc a l2] in
      let q1 = replace l l1 in
      let q2 = replace l (List.remove_assoc a l2) in
      newcut l (List.assoc a l2)
	(List.fold_left ladapt proof1 q1)
	(List.fold_left ladapt proof2 q2)
    | SClor (a, b, _, _), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l =
	merge [List.remove_assoc a l1; List.remove_assoc b l2] in
      let q1 = replace l (List.remove_assoc a l1) in
      let q2 = replace l (List.remove_assoc b l2) in
      let c3 = unify c1 c2 in
      (eor (a, b), eor (List.assoc a l1, List.assoc b l2)) :: l,
      sclor (
	List.assoc a l1, List.assoc b l2,
	radapt (List.fold_left ladapt proof1 q1) (c1, c3),
	radapt (List.fold_left ladapt proof2 q2) (c2, c3))
    | SClimply (a, b, _, _), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; List.remove_assoc b l2] in
      let b2 = List.assoc b l2 in
      let q1 = replace l l1 in
      let q2 = replace l (List.remove_assoc b l2) in
      (eimply (a, b), eimply (c1, List.assoc b l2)) :: l,
      sclimply (
	c1, b2,
	List.fold_left ladapt proof1 q1,
	List.fold_left ladapt proof2 q2)
    | SCrand (a, b, _, _), [l1; l2],
      [(g1, c1, _) as proof1; (g2, c2, _) as proof2] ->
      let l = merge [l1; l2] in
      let q1 = replace l l1 in
      let q2 = replace l l2 in
      l, scrand (
	c1, c2,
	List.fold_left ladapt proof1 q1,
	List.fold_left ladapt proof2 q2)
    | SClcontr (a, _), [l], [(g, c, _) as proof] ->
      let a1 = List.assoc a l in
      let a2 = List.assoc a (List.remove_assoc a l) in
      let a3 = unify
	(List.assoc a l)
	(List.assoc a (List.remove_assoc a l)) in
      (a, a3)
      :: List.remove_assoc a (List.remove_assoc a l),
      sclcontr (a3, ladapt (ladapt proof (a1, a3)) (a2, a3))
    | SCaxiom _, _, _ | SCfalse, _, _
    | SCtrue, _, _ | SCeqref _, _, _ | SCeqsym _, _, _
    | SCeqfunc _, _, _
      -> List.map (fun x -> (x, x)) lkg, lkproof
    | SCeqprop _, _ , _
      ->
	List.map (fun x -> (x, x)) lkg, lkproof
    | SCrweak (a, _), [l], [(g, c, _) as proof] ->
      l, scrweak (a, proof)
    | SCland (a, b, _), [l], [(g, c, _) as proof] ->
      (eand (a, b), eand (List.assoc a l,List.assoc b l))
      :: (List.remove_assoc a (List.remove_assoc b l)),
      scland (List.assoc a l, List.assoc b l, proof)
    | SClnot (e, _), [l], [(g, c, _) as proof] ->
      (enot e, enot c) :: l, sclnot (c, proof)
    | SCrorl (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorl (c, b, proof)
    | SCrorr (a, b, _), [l], [(g, c, _) as proof] ->
      l, scrorr (a, c, proof)
    | SCrimply (a, b, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l, scrimply (List.assoc a l, c, proof)
    | SCrnot (a, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc a l,
      scrnot (List.assoc a l, proof)
    | SClall (Eall (x, ty, e, _) as ap, t, _),
      [l], [(g, c, _) as proof] ->
      let h = eall (
	x, ty,
	weaken e (List.assoc (substitute [(x, t)] e) l)) in
      (ap, h) :: (List.remove_assoc (substitute [(x, t)] e) l),
      sclall (h, t, proof)
    | SClex (Eex (x, ty, e, _) as ep, v, _),
      [l], [(g, c, _) as proof] ->
      let h = eex (
	x, ty,
	weaken e (List.assoc (substitute [(x, v)] e) l)) in
      (ep, h) :: (List.remove_assoc (substitute [(x, v)] e) l),
      sclex (h, v, proof)
    | SCrall (Eall (x, ty, e, _), v, _), [l],
      [(g, c, _) as proof] ->
      l, scrall (eall (x, ty, weaken e c), v, proof)
    | SCrex (Eex (x, ty, e, _), t, _), [l], [(g, c, _) as proof] ->
      l, screx (eex (x, ty, weaken e c), t, proof)
    | SCcnot (e, _), [l], [(g, c, _) as proof] ->
      List.remove_assoc (enot e) l,
      scrnot (List.assoc (enot e) l, proof)
    | _, _, _ -> assert false in
  let ljg, _, _ = ljprf in
  assert (List.length lkg = List.length ljg);
  assert (List.length ljlist = List.length ljg);
  ljlist, ljprf

let rec lltolj proof goal =
  let result = match goal with
    | Some (Enot (g, _)) ->
      let newgoal = use_defs g in
      let newproof = use_defs_proof proof in
      newgoal, lefttoright newgoal (
	lltolk newproof (Some (enot newgoal)))
    | None ->
      let newproof = use_defs_proof proof in
      efalse, lltolk newproof None;
    | _ -> assert false in
  let conc, lkproof = List.fold_left
    (fun (conc, rule) stmt ->
      let newstmt = use_defs stmt in
      eimply (newstmt, conc),
      scrimply (newstmt, conc, rule)
    )
    result !hypothesis_env in
  let _, ljproof = lltoljrule (*optimize lkproof*) lkproof in
  ljproof
