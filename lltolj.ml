open Printf;;
open Expr;;
open Llproof;;
open Namespace;;

exception Found of expr;;

let p_debug s es = 
  eprintf "%s |" s;
  List.iter
    (eprintf " %a |" 
       (fun oc x -> Print.expr (Print.Chan oc) x)
    ) es; 
  eprintf "\n";
;;

type sequent = expr list * expr list

type lkrule =
| SCaxiom of expr
| SCfalse
| SCtrue
| SCeqref of expr
| SCeqsym of expr * expr
| SCeqprop of expr * expr * lkproof list
| SCeqfunc of expr * expr * lkproof list
| SCcut of expr * lkproof * lkproof
| SCland of expr * expr * lkproof
| SClor of expr * expr * lkproof * lkproof
| SClimply of expr * expr * lkproof * lkproof
| SClnot of expr * lkproof
| SClall of expr * expr * lkproof
| SClex of expr * expr * lkproof
| SClcongruence of expr * expr * expr * lkproof
| SCrand of expr * expr * lkproof * lkproof
| SCrorl of expr * expr * lkproof
| SCrorr of expr * expr * lkproof
| SCrimply of expr * expr * lkproof
| SCrnot of expr * lkproof
| SCrall of expr * expr * lkproof
| SCrex of expr * expr * lkproof
| SCrcongruence of expr * expr * expr * lkproof
| SCrcontr of expr * lkproof

and lkproof = 
  expr list * expr list * lkrule
;;

let rec rm a list =
  match list with
  | x :: list when equal x a -> list
  | x :: list -> x :: (rm a list)
  | [] -> assert false
;;

let scaxiom (e, g, d) = e :: g, e :: d, SCaxiom e;;
let scfalse (g, d) = efalse :: g, d, SCfalse;;
let sctrue (g, d) = g, etrue :: d, SCtrue;;
let sceqref (a, g, d) = g, eapp ("=", [a; a]) :: d, SCeqref (a);;
let sceqsym (a, b, g, d) =
  eapp ("=", [a; b]) :: g, 
  eapp ("=", [b; a]) :: d, SCeqsym (a, b);;
let sceqprop (e1, e2, proofs) =
  match proofs with
  | [] -> [e1], [e2], SCeqprop (e1, e2, [])
  | (g, d, rule) as proof :: proofs ->
    match e1, e2 with
    | Eapp (x, t :: ts, _), Eapp (y, u :: us, _) ->
      e1 :: g, e2 :: rm (eapp ("=", [t; u])) d, 
      SCeqprop (e1, e2, proof :: proofs)
    | _ -> assert false;;
let sceqfunc (e1, e2, proofs) =
  match proofs with
  | [] -> [e1], [e2], SCeqprop (e1, e2, [])
  | (g, d, rule) as proof :: proofs ->
    match e1, e2 with
    | Eapp (x, t :: ts, _), Eapp (y, u :: us, _) ->
      e1 :: g, e2 :: rm (eapp ("=", [t; u])) d, 
      SCeqfunc (e1, e2, proof :: proofs)
    | _ -> assert false
let sccut (e, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  g1, rm e d1, SCcut(e, proof1, proof2);;
let scland (e1, e2, proof) = 
  let (g, d, rule) = proof in
  (eand (e1, e2)) :: rm e1 (rm e2 g), d, SCland (e1, e2, proof);;
let sclor (e1, e2, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  (eor (e1, e2)) :: rm e1 g1, d1, SClor (e1, e2, proof1, proof2);;
let sclimply (e1, e2, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  (eimply (e1, e2)) :: g1, rm e1 d1, 
  SClimply (e1, e2, proof1, proof2);;
let sclnot (e, proof) = 
  let (g, d, rule) = proof in
  (enot e) :: g, rm e d, SClnot (e, proof);;
let sclall (e1, t, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, d, rule) = proof in
    e1 :: rm (substitute [(x, t)] p) g, d, SClall (e1, t, proof)
  | _ -> assert false;;
let sclex (e1, v, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
    let (g, d, rule) = proof in
    e1 :: rm (substitute [(x, v)] p) g, d, SClex (e1, v, proof)
  | _ -> assert false;;
let sclcongruence (p, a, b, proof) = 
  let (g, d, rule) = proof in
  apply p a :: eapp ("=", [a; b]) :: (rm (apply p b) g), 
  d, SClcongruence (p, a, b, proof);;
let scrand (e1, e2, proof1, proof2) = 
  let (g1, d1, rule1) = proof1 in
  g1, eand (e1, e2) :: rm e1 d1, SCrand (e1, e2, proof1, proof2);;
let scrorl (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2) :: rm e1 d, SCrorl (e1, e2, proof);;
let scrorr (e1, e2, proof) = 
  let (g, d, rule) = proof in
  g, eor (e1, e2) :: rm e2 d, SCrorr (e1, e2, proof);;
let scrimply (e1, e2, proof) = 
  let (g, d, rule) = proof in
  rm e1 g, eimply (e1, e2) :: rm e2 d, SCrimply (e1, e2, proof);;
let scrnot (e, proof) = 
  let (g, d, rule) = proof in
  rm e g, enot e :: d, SCrnot (e, proof);;
let scrall (e1, v, proof) = 
  match e1 with
  | Eall (x, ty, p, _) ->
    let (g, d, rule) = proof in
    g, e1 :: rm (substitute [(x, v)] p) d, SCrall (e1, v, proof)
  | _ -> assert false;;
let screx (e1, t, proof) = 
  match e1 with
  | Eex (x, ty, p, _) ->
      let (g, d, rule) = proof in
      g, e1 :: rm (substitute [(x, t)] p) d, SCrex (e1, t, proof)
  | _ -> assert false;;
let scrcongruence (p, a, b, proof) = 
  let (g, d, rule) = proof in
  eapp ("=", [a; b]) :: g, apply p a :: (rm (apply p b) d), 
  SCrcongruence (p, a, b, proof);;
let scrcontr (e, proof) = 
  let (g, d, rule) = proof in
  g, rm e d, SCrcontr (e, proof);;

let lemma_env = 
  (Hashtbl.create 97 : (string, prooftree) Hashtbl.t)
;;

let hypothesis_env = ref [];;

let definition_env =
  (Hashtbl.create 97 : (string, expr list * expr) Hashtbl.t)
;;

let hypsofrule lkrule =
  match lkrule with
  | SCaxiom (e) -> []
  | SCfalse -> []
  | SCtrue -> []
  | SCeqref (e) -> []
  | SCeqsym (e1, e2) -> []
  | SCeqprop (e1, e2, proofs) -> proofs
  | SCeqfunc (e1, e2, proofs) -> proofs
  | SCcut (e, proof1, proof2) -> [proof1; proof2]
  | SCland (e1, e2, proof) -> [proof]
  | SClor (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClimply (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SClnot (e, proof) -> [proof]
  | SClall (e1, e2, proof) -> [proof]
  | SClex (e1, e2, proof) -> [proof]
  | SClcongruence (p, a, b, proof) -> [proof]
  | SCrand (e1, e2, proof1, proof2) -> [proof1; proof2]
  | SCrorl (e1, e2, proof) -> [proof]
  | SCrorr (e1, e2, proof) -> [proof]
  | SCrimply (e1, e2, proof) -> [proof]
  | SCrnot (e, proof) -> [proof]
  | SCrall (e1, e2, proof) -> [proof]
  | SCrex (e1, e2, proof) -> [proof]
  | SCrcongruence (p, a, b, proof) -> [proof]
  | SCrcontr (e, proof) -> [proof]
;;

let applytohyps f lkproof =
  let g, d, lkrule = lkproof in
  match lkrule with
  | SCaxiom (e) -> g, d, SCaxiom (e)
  | SCfalse -> g, d, SCfalse
  | SCtrue -> g, d, SCtrue
  | SCeqref (e) -> g, d, SCeqref (e)
  | SCeqsym (e1, e2) -> g, d, SCeqsym (e1, e2)
  | SCeqprop (e1, e2, proofs) -> 
    sceqprop (e1, e2, List.map f proofs)
  | SCeqfunc (e1, e2, proofs) -> 
    sceqfunc (e1, e2, List.map f proofs)
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
  | SClcongruence (p, a, b, proof) -> 
    sclcongruence (p, a, b, f proof)
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
  | SCrcongruence (p, a, b, proof) -> 
    scrcongruence (p, a, b, f proof)
  | SCrcontr (e, proof) -> scrcontr (e, f proof)
;;

let rec xaddhyp h lkproof =
  let g, d, lkrule = lkproof in 
  match lkrule with
  | SCaxiom _ | SCfalse 
  | SCtrue | SCeqref _ | SCeqsym _ -> 
    h :: g, d, lkrule
  | _ -> applytohyps (xaddhyp h) lkproof
    
and rmhyps hyps g = 
  match hyps with
  | h :: hs when List.mem h g -> rmhyps hs (rm h g)
  | h :: hs -> h :: rmhyps hs g
  | [] -> []
    
and addhyp hyps lkproof =
  let g, d, lkrule = lkproof in
  List.fold_left (fun pf h -> xaddhyp h pf) lkproof (rmhyps hyps g)
;;

let rec addconc c lkproof =
  let g, d, lkrule = lkproof in
  match lkrule with
  | SCaxiom _ | SCfalse 
  | SCtrue | SCeqref _ | SCeqsym _ -> 
    g, c :: d, lkrule
  | _ -> applytohyps (addconc c) lkproof
  

let rec use_defs e = 
  match e with
  | Evar (v, _) when Hashtbl.mem definition_env v -> 
    let (params, body) = Hashtbl.find definition_env v in
    body
  | Eapp (s, args, _) when Hashtbl.mem definition_env s ->
    let exprs = List.map use_defs args in
    let (params, body) = Hashtbl.find definition_env s in
    substitute (List.combine params exprs) body
  | Evar (_, _) | Etrue | Efalse -> e
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
    etau (x, s, use_defs e)
  | Elam (x, s, e, _) ->
    elam (x, s, use_defs e)
  | Emeta _ -> 
    assert false

and use_defs_rule rule =
  match rule with
  | Rfalse -> Rfalse
  | Rnottrue -> Rnottrue
  | Raxiom (p) -> Raxiom (use_defs p)
  | Rcut (p) -> Rcut (use_defs p)
  | Rnoteq (a) -> Rnoteq (a)
  | Reqsym (a, b) -> Reqsym (a, b)
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
  | RcongruenceLR (p, a, b) -> RcongruenceLR (use_defs p, a, b)
  | RcongruenceRL (p, a, b) -> RcongruenceRL (use_defs p, a, b)
  | Rdefinition (name, sym, args, body, recarg, c, h) -> 
    rule
  | Rextension (ext, name, args, cons, hyps) ->
    Rextension (
      ext, name, List.map use_defs args, 
      List.map use_defs cons, List.map (List.map use_defs) hyps)
  | Rlemma (name, args) -> rule
;;

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
    | Equiv -> [[enot p; enot q]; [p; q]], [eequiv (p, q)]  end
  | Rnotconnect (b, p, q) -> 
    begin match b with
    | And -> [[enot p]; [enot q]], [enot (eand (p, q))]
    | Or -> [[enot p; enot q]], [enot (eor (p, q))]
    | Imply -> [[p; enot q]], [enot (eimply (p, q))]
    | Equiv -> 
      [[enot p; q]; [p; enot q]], [enot (eequiv (p, q))]  end
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
    let g, d, rule = lltolk (Hashtbl.find lemma_env name) None in
    [], g
  | _ -> assert false

and lltolk proof goal =
  let pregamma = 
    match goal with
    | Some (Enot (g, _)) -> enot g :: !hypothesis_env
    | None -> !hypothesis_env
    | _ -> assert false in
  let gamma = List.map use_defs pregamma in
  lltolkrule proof gamma

and righttoleft e proof =
  sclnot (e, proof)

and lefttoright expr lkproof =
  let g, d, lkrule = lkproof in
  match lkrule with
  | SClnot (e, proof) 
      when equal expr e ->
    proof
  | SClcongruence (p, a, b, proof) 
      when equal (enot expr) (apply p a) -> 
    begin match p with
    | Elam (v, ty, Enot (f, _), _) -> 
      let q = elam (v, ty, f) in
      scrcongruence (q, a, b, lefttoright (apply q b) proof)
    | _ -> assert false end
  | SCaxiom (e) 
    when equal e (enot expr) ->
    scrnot (expr, scaxiom (expr, rm e g, rm e d))
  | SCaxiom _ | SCfalse 
  | SCtrue | SCeqref _ | SCeqsym _ ->
    rm (enot expr) g, expr :: d, lkrule
  | _ -> applytohyps (lefttoright expr) lkproof

and lltolkrule proof gamma =
  let rule = use_defs_rule proof.rule in 
  (*is use_defs_rule necessary ?*)
  let prehypslist, preconclist = hypstoadd rule in
  let hypslist = List.map (List.map use_defs) prehypslist in
  let conclist = List.map use_defs preconclist in
  let list = 
    List.fold_left (fun es e -> rm e es) 
      gamma conclist in
  let hyps = 
    List.map2 lltolkrule proof.hyps 
      (List.map (List.rev_append list) hypslist) in
  addhyp gamma (xlltolkrule rule hyps list)

and xlltolkrule rule hyps gamma =
  match rule, hyps with
  | Rfalse, [] ->
    scfalse (gamma, [])
  | Rnottrue, [] ->
    righttoleft etrue (sctrue (gamma, []))
  | Raxiom (p), [] -> 
    righttoleft p (scaxiom (p, gamma, []))
  | Rcut (p), [proof1; proof2] -> 
    sccut (p, lefttoright p proof2, proof1)
  | Rnoteq (a), [] -> 
    righttoleft (eapp ("=", [a; a])) (sceqref (a, gamma, []));
  | Reqsym (a, b), [] ->
    righttoleft (eapp ("=", [b; a]))
      (sceqsym (a, b, gamma, []))
  | Rnotnot (p), [proof] ->
    righttoleft (enot (p))
      (scrnot (p, proof))
  | Rconnect (And, p, q), [proof] ->
    scland (p, q, proof)
  | Rconnect (Or, p, q), [proof1; proof2] ->
    sclor (p, q, proof1, proof2)
  | Rconnect (Imply, p, q), [proof1; proof2] ->
    sclimply (p, q, lefttoright p proof1, proof2)
  | Rconnect (Equiv, p, q), [proof1; proof2] ->
    scland (
      eimply (p, q), eimply (q, p),
      sclimply (
	p, q,
	sclimply (
	  q, p, 
	  lefttoright p (lefttoright q proof1), 
	  scaxiom (p, gamma, [])),
	sclimply (
	  q, p, 
	  scaxiom (q, gamma, []), proof2)))
  | Rnotconnect (And, p, q), [proof1; proof2] ->
    righttoleft (eand (p, q))
      (scrand (p, q, lefttoright p proof1, lefttoright q proof2))
  | Rnotconnect (Or, p, q), [proof] ->
    righttoleft (eor (p, q))
      (scrcontr
	 (eor (p, q), scrorl 
	   (p, q, scrorr 
	     (p, q, lefttoright p (lefttoright q proof)))))
  | Rnotconnect (Imply, p, q), [proof] -> 
    righttoleft (eimply (p, q))
      (scrimply (p, q, lefttoright q proof))
  | Rnotconnect (Equiv, p, q), [proof1; proof2] ->
    righttoleft (eand (eimply (p, q), eimply (q, p)))
      (scrand (eimply (p, q), eimply (q, p), 
	       scrimply (p, q, lefttoright q proof2),
	       scrimply (q, p, lefttoright p proof1)))
  | Rex (ep, v), [proof] ->
    sclex (ep, v, proof)
  | Rall (ap, t), [proof] ->
    sclall (ap, t, proof)
  | Rnotex (Eex(x, ty, p, _) as ep, t), [proof] ->
    righttoleft ep
      (screx (ep, t, lefttoright (substitute [(x, t)] p) proof))
  | Rnotall (Eall(x, ty, p, _) as ap, v), [proof] ->
    righttoleft ap
      (scrall (ap, v, lefttoright (substitute [(x, v)] p) proof))
  | Rpnotp (Eapp (p, ts, _), Enot (Eapp (q, us, _), _)), proofs ->
    righttoleft (eapp (q, us))
      (sceqprop (
	eapp (p, ts), eapp (q, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | Rnotequal (Eapp (f, ts, _), Eapp (g, us, _)), 
    proofs ->
    righttoleft (eapp ("=", [eapp (f, ts); eapp (g, us)]))
      (sceqfunc (
	eapp (f, ts), eapp (g, us), 
	List.map2 lefttoright 
	  (List.map2 
	     (fun t u -> eapp ("=", [t; u])) ts us) proofs))
  | RcongruenceLR (p, a, b), [proof] ->
    sclcongruence (p, a, b, proof)
  | RcongruenceRL (p, a, b), [proof] ->
    sccut (
      eapp ("=", [a; b]),
      sceqsym (b, a, gamma, []),
      sclcongruence (p, a, b, proof)) 
  | Rdefinition (name, sym, args, body, recarg, fld, unf), [proof] 
    -> proof
  | Rextension ("", "zenon_notallex", [Elam (v, t, p, _)], 
		[Enot (Eall (x, s, e, _) as ap, _)], [[ep]]), 
      [proof] ->
    let q = substitute [(v, etau (x, s, enot e))] p in
    righttoleft (ap)
      (scrall (ap, etau (x, s, enot e), sccut (
	ep,
	screx (
	  ep, etau (x, s, enot e), 
	  scrnot (q, scaxiom (q, gamma, []))),
	addconc q proof)))
  | Rextension (ext, name, args, cons, hyps), proofs -> 
    assert false
  | Rlemma (name, args), [] -> 
    let proof = Hashtbl.find lemma_env name in
    lltolk proof None
  | _ -> assert false
;;

let cl e = match e with
  | Etrue -> enot (enot (etrue))
  | Efalse -> enot (enot (efalse))
  | Evar (s, _) -> evar (s);
  | Eapp ("=", args, _) -> enot (enot (eapp ("=", args)))
  | Eapp (s, args, _) -> eapp (s, args)
  | Eand (e1, e2, _) -> 
    enot (enot (eand (enot (enot e1),enot (enot e2))))
  | Eor (e1, e2, _) ->
    enot (enot (eor (enot (enot e1),enot (enot e2))))
  | Eimply (e1, e2, _) ->
    enot (enot (eimply (enot (enot e1),enot (enot e2))))
  | Enot (e, _) -> enot (enot (enot (enot (enot e))))
  | Eall (Evar (v, _), s, e, _) ->
    enot (enot (eall (evar (v), s, enot (enot e))))
  | Eex (Evar (v, _), s, e, _) ->
    enot (enot (eex (evar (v), s, enot (enot e))))
  | Eex _ | Eall _ | Etau _ 
  | Elam _ | Emeta _ | Eequiv _ -> 
    assert false
;;

let rec ll e = match e with
  | Etrue | Efalse 
  | Evar _ | Eapp _ -> cl e
  | Eand (e1, e2, _) -> cl (eand (ll e1, ll e2))
  | Eor (e1, e2, _) -> cl (eor (ll e1, ll e2))
  | Eimply (e1, e2, _) -> cl (eimply (ll e1, ll e2))
  | Enot (e, _) -> cl (enot (ll e))
  | Eall (Evar (v, _), s, e, _) -> cl (eall (evar v, s, ll e))
  | Eex (Evar (v, _), s, e, _) -> cl (eex (evar v, s, ll e))
  | Eex _ | Eall _ | Etau _ 
  | Elam _ | Emeta _ | Eequiv _ -> 
    assert false

and l e = match e with
  | Etrue -> etrue
  | Efalse -> efalse
  | Evar (s, _) -> evar (s)
  | Eapp ("=", args, _) -> enot (enot (eapp ("=", args)))
  | Eapp (s, args, _) -> eapp (s, args)
  | Eand (e1, e2, _) -> 
    eand (enot (enot (ll e1)),enot (enot (ll e2)))
  | Eor (e1, e2, _) -> 
    eor (enot (enot (ll e1)),enot (enot (ll e2)))
  | Eimply (e1, e2, _) -> 
    eimply (enot (enot (ll e1)),enot (enot (ll e2)))
  | Enot (e, _) -> enot (enot (enot (ll e)))
  | Eall (Evar (v, _), s, e, _) ->
    eall (evar (v), s, enot (enot (ll e)))
  | Eex (Evar (v, _), s, e, _) ->
    eex (evar (v), s, enot (enot (ll e)))
  | Eex _ | Eall _ | Etau _ 
  | Elam _ | Emeta _ | Eequiv _ -> 
    assert false
;;

let lnotnot e proof =
  sclnot (enot (e), scrnot (e, proof))
;;

let lll e f rule=
  if equal (l e) (ll e)
  then rule
  else f rule
;;

let rec lltolj proof goal =
  let result = match goal with 
    | Some (Enot (g, _)) -> 
      let newgoal = use_defs g in
      newgoal, lefttoright newgoal (lltolk proof goal)
    | None ->
      efalse, addconc efalse (lltolk proof goal);
    | _ -> assert false in
  let conc, lkproof = List.fold_left
    (fun (conc, rule) stmt ->
      let newstmt = use_defs stmt in
      eimply (newstmt, conc), 
      scrimply (newstmt, conc, addhyp [newstmt] rule)
    )
    result !hypothesis_env in
  let ljrule = lltoljrule lkproof in
  scrnot (enot (l conc), ljrule)
    
and lltoljrule proof =
  let g, d, rule = proof in
  match rule,
    List.map lltoljrule (hypsofrule rule) with
  | SCaxiom (e), [] -> 
    assert (List.mem e g & List.mem e d);
    let gamma = 
      List.map l (rm e g) @ 
	List.map (fun e -> enot (l e)) (rm e d) in 
    righttoleft (l e) 
      (scaxiom (l e, gamma, []))
  | SCfalse, [] -> 
    assert (List.mem efalse g);
    let gamma = 
      List.map l (rm efalse g) @ 
	List.map (fun e -> enot (l e)) d in
    scfalse (gamma, [])
  | SCtrue, [] ->
    assert (List.mem etrue d);
    let gamma = 
      List.map l g @ 
	List.map (fun e -> enot (l e)) (rm etrue d) in 
    righttoleft (etrue) 
      (sctrue (gamma, []))
  | SCeqref (a), [] -> 
    assert (List.mem (eapp ("=", [a; a])) d);
    let gamma = 
      List.map l g @ 
	List.map (fun e -> enot (l e)) 
	(rm (eapp ("=", [a; a])) d) in 
    lnotnot (enot (eapp ("=", [a; a])))
      (righttoleft (eapp ("=", [a; a])) 
	 (sceqref (a, gamma, [])))
  | SCeqsym (a, b), [] ->
    assert (List.mem (eapp ("=", [a; b])) g &
	      List.mem (eapp ("=", [b; a])) d);
    let gamma = 
      List.map l (rm (eapp ("=", [a; b])) g) @ 
	List.map (fun e -> enot (l e)) 
	(rm (eapp ("=", [b; a])) d) in 
    lnotnot (eapp ("=", [a; b]))
      (lnotnot (enot (eapp ("=", [b; a])))
	 (righttoleft (eapp ("=", [b; a])) 
	    (sceqsym (a, b, gamma,[]))))
  | SCcut (e, _, _), [proof1; proof2] ->
    sccut (enot (l e), scrnot (l e, proof2), proof1)
  | SCland (e1, e2, _), [proof] ->
    scland 
      (enot (enot (ll e1)), enot (enot (ll e2)), 
       lnotnot (ll e1)
	 (lnotnot (ll e2)
	    (lll e1 (lnotnot (l e1))
	       (lll e2 (lnotnot (l e2)) proof))))
  | SClor (e1, e2, _, _), [proof1; proof2] ->
    sclor (
      enot (enot (ll e1)), enot (enot (ll e2)),  
      lnotnot (ll e1)
        (lll e1 (lnotnot (l e1)) proof1),
      lnotnot (ll e2)
	(lll e2 (lnotnot (l e2)) proof2))
  | SClimply (e1, e2, _, _), [proof1; proof2] ->
    sclimply (
      enot (enot (ll e1)), enot (enot (ll e2)),
      scrnot (
	enot (ll e1),
	(lll e1 (lnotnot (enot (l e1))) proof1)),
      lnotnot (ll e2)
	(lll e2 (lnotnot (l e2)) proof2))
  | SClnot (e, _), [proof] ->
    lnotnot (enot (ll e))
      (lll e (lnotnot (enot (l e))) proof)
  | SClall (Eall (x, ty, p, _) as ap, t, _), [proof] ->
    let q = substitute [(x, t)] p in
    sclall (
      l ap, t, 
      lnotnot (ll q)
	(lll q (lnotnot (l q)) proof))
  | SClex (Eex (x, ty, p, _) as ep, v, _), [proof] ->
    let q = substitute [(x, v)] p in
    sclex (
      l ep, v,
      lnotnot (ll q)
	(lll q (lnotnot (l q)) proof))
  | SClcongruence (Elam (x, t, e, _), a, b, _), [proof] -> 
    lnotnot (eapp ("=", [a; b]))
      (sclcongruence (elam (x, t, l e), a, b, proof))
  | SCrand (e1, e2, _, _), [proof1; proof2] ->
    righttoleft (l (eand (e1, e2)))
      (scrand (
	enot (enot (ll e1)), enot (enot (ll e2)), 
	scrnot (
	  enot (ll e1), 
	  (lll e1 (lnotnot (enot (l e1))) proof1)),
	scrnot (
	  enot (ll e2), 
	  (lll e2 (lnotnot (enot (l e2))) proof2))))
  | SCrorl (e1, e2, _), [proof] ->
    righttoleft (l (eor (e1, e2))) 
      (scrorl (
	enot (enot (ll e1)), enot (enot (ll e2)),
	scrnot (
	  enot (ll e1), 
	  lll e1 (lnotnot (enot (l e1))) proof)))
  | SCrorr (e1, e2, _), [proof] ->
      righttoleft (l (eor (e1, e2)))
	(scrorr (
	  enot (enot (ll e1)), enot (enot (ll e2)),	
	  scrnot (
            enot (ll e2),
	    lll e2 (lnotnot (enot (l e2))) proof)))
  | SCrimply (e1, e2, _), [proof] ->
    righttoleft (l (eimply (e1, e2)))
      (scrimply (
	enot (enot (ll e1)), enot (enot (ll e2)),
	scrnot (
	  enot (ll e2),
	  lll e2 (lnotnot (enot (l e2)))
	    (lnotnot (ll e1)
	       (lll e1 (lnotnot (l e1)) proof)))))
  | SCrnot (e, _), [proof] ->
    lnotnot (enot (enot (ll e)))
      (lnotnot (ll e)
	 (lll e (lnotnot (l e)) proof))
  | SCrall (Eall (x, ty, p, _) as ap, v, _), [proof] ->
    let q = substitute [(x, v)] p in
    righttoleft (l ap)
      (scrall (
	l ap, v,
	scrnot (
	  enot (ll q), 
	  lll q (lnotnot (enot (l q))) proof)))
  | SCrex (Eex (x, ty, p, _) as ep, t, _), [proof] ->
    let q = substitute [(x, t)] p in
    righttoleft (l ep)
      (screx (
	l ep, t,
	scrnot (
	  enot (ll q), 
	  lll q (lnotnot (enot (l q))) proof)))
  | SCrcongruence (Elam (x, ty, e, _), a, b, _), [proof] ->
    lnotnot (eapp ("=", [a; b]))
      (sclcongruence (elam (x, ty, enot (l e)), a, b, proof))
  | SCrcontr (e, lkproof), [proof] -> 
    let g, d, rule = proof in
    rm (enot (l e)) g, d, rule
  | _ -> assert false
;;

