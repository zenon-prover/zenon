(*  Copyright 2004 INRIA  *)
Version.add "$Id: tptp.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

open Expr;;
open Phrase;;

let equality_axioms = [
  eall ("x", "", eapp ("=", [evar "x"; evar "x"]));
  eall ("x", "",
    eall ("y", "", eimply (eapp ("=", [evar "x"; evar "y"]),
                           eapp ("=", [evar "y"; evar "x"]))));
  eall ("x", "",
    eall ("y", "",
      eall ("z", "",
        eimply (eand (eapp ("=", [evar "x"; evar "y"]),
                      eapp ("=", [evar "y"; evar "z"])),
                eapp ("=", [evar "x"; evar "z"])))));
];;

let check_arg context v1 v2 a1 a2 =
  match a1, a2 with
  | Evar (w1, _), Evar (w2, _) ->
      w1 = w2 && List.mem w1 context
      || w1 = v1 && w2 = v2
      || w1 = v2 && w2 = v1
  | _, _ -> false
;;

let rec equ_form context f =
  match f with
  | Eall (v, t, g, _) -> equ_form (v::context) g
  | Eimply (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _),
            Eapp ("=", [Eapp (s1, l1, _); Eapp (s2, l2, _)], _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | Eimply (Eand (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _),
                  Eapp (s1, l1, _), _),
            Eapp (s2, l2, _), _) ->
      s1 = s2 && List.mem v1 context && List.mem v2 context
      && List.for_all2 (check_arg context v1 v2) l1 l2
  | _ -> false
;;

let is_eq_formula f =
  List.exists (Expr.equal f) equality_axioms
  || equ_form [] f
;;

let is_var v = String.length v > 0 && v.[0] >= 'A' && v.[0] <= 'Z';;

let check_clause_arg v1 v2 a1 a2 =
  match a1, a2 with
  | Evar (w1, _), Evar (w2, _) ->
      w1 = w2 && is_var w1
      || w1 = v1 && w2 = v2
      || w1 = v2 && w2 = v1
  | _, _ -> false
;;

let is_eq_clause = function
  | [ Eapp ("=", [Evar (v1, _); Evar (v2, _)], _) ] -> v1 = v2

  | [ Eapp ("=", [Evar (v1, _); Evar (v2, _)], _);
      Enot (Eapp ("=", [Evar (v3, _); Evar (v4, _)], _), _);
    ]
  | [ Enot (Eapp ("=", [Evar (v3, _); Evar (v4, _)], _), _);
      Eapp ("=", [Evar (v1, _); Evar (v2, _)], _);
    ] -> v1 = v4 && v2 = v3

  | [ Eapp ("=", [Evar (v1, _); Evar (v2, _)], _);
      Enot (Eapp ("=", [Evar (v3, _); Evar (v4, _)], _), _);
      Enot (Eapp ("=", [Evar (v5, _); Evar (v6, _)], _), _);
    ]
  | [ Enot (Eapp ("=", [Evar (v3, _); Evar (v4, _)], _), _);
      Eapp ("=", [Evar (v1, _); Evar (v2, _)], _);
      Enot (Eapp ("=", [Evar (v5, _); Evar (v6, _)], _), _);
    ]
  | [ Enot (Eapp ("=", [Evar (v5, _); Evar (v6, _)], _), _);
      Enot (Eapp ("=", [Evar (v3, _); Evar (v4, _)], _), _);
      Eapp ("=", [Evar (v1, _); Evar (v2, _)], _);
    ] ->
      v1 = v3 && v4 = v5 && v6 = v2  ||  v1 = v5 && v6 = v3 && v4 = v2

  | [ Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
      Enot (Eapp (s1, a1, _), _);
      Eapp (s2, a2, _);
    ]
  | [ Enot (Eapp (s1, a1, _), _);
      Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
      Eapp (s2, a2, _);
    ]
  | [ Enot (Eapp (s1, a1, _), _);
      Eapp (s2, a2, _);
      Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
    ]
  | [ Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
      Eapp (s2, a2, _);
      Enot (Eapp (s1, a1, _), _);
    ]
  | [ Eapp (s2, a2, _);
      Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
      Enot (Eapp (s1, a1, _), _);
    ]
  | [ Eapp (s2, a2, _);
      Enot (Eapp (s1, a1, _), _);
      Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
    ] ->
      s1 = s2 && is_var v1 && is_var v2
      && List.for_all2 (check_clause_arg v1 v2) a1 a2

  | [ Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
      Eapp ("=", [Eapp (s1, a1, _); Eapp (s2, a2, _)], _);
    ]
  | [ Eapp ("=", [Eapp (s1, a1, _); Eapp (s2, a2, _)], _);
      Enot (Eapp ("=", [Evar (v1, _); Evar (v2, _)], _), _);
    ] ->
      s1 = s2 && is_var v1 && is_var v2
      && List.for_all2 (check_clause_arg v1 v2) a1 a2

  | _ -> false
;;

let clauses = ref [];;

let rec trans dir ps =
  match ps with
  | [] -> []
  | Include f :: t -> (try_incl dir f) @ (trans dir t)
  | Clause (name, kind, body) :: t ->
      if is_eq_clause body
      then trans dir t
      else begin
        clauses := body :: !clauses;
        trans dir t
      end
  | Formula (name, "axiom", body) :: t ->
      if is_eq_formula body
      then trans dir t
      else (body, 2) :: (trans dir t)
  | Formula (name, "hypothesis", body) :: t ->
      if is_eq_formula body
      then trans dir t
      else (body, 1) :: (trans dir t)
  | Formula (name, "conjecture", body) :: t ->
      (enot (body), 0) :: (trans dir t)
  | Formula (name, k, body) :: t ->
      raise (Failure ("unknown formula kind: "^k))

and try_incl dir f =
  try
    incl dir (Filename.concat dir f)
  with Sys_error _ ->
    let pp = Filename.parent_dir_name in
    let name = List.fold_left Filename.concat dir [pp; pp; f] in
    incl dir name

and incl dir name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let tpphrases = Parser.tpfile Lexer.tptoken lexbuf in
  close_in chan;
  trans dir tpphrases
;;

let rec element e l =
  match l with
  | [] -> false
  | h :: t when Expr.equal e h -> true
  | h :: t -> element e t
;;

let rec remove e l =
  match l with
  | [] -> []
  | h :: t when Expr.equal e h -> remove e t
  | h :: t -> h :: (remove e t)
;;

let mkor e1 e2 =
  match e1, e2 with
  | Efalse, _ -> e2
  | _, Efalse -> e1
  | _, _ -> eor (e1, e2)
;;

let mkand e1 e2 =
  match e1, e2 with
  | Enot (Efalse, _), _ -> e2
  | _, Enot (Efalse, _) -> e1
  | _, _ -> eand (e1, e2)
;;

module HE = Hashtbl.Make (Expr);;

let rec factor_clauses l =
  let t = HE.create 97 in
  let count t e =
    try incr (HE.find t e)
    with Not_found -> HE.add t e (ref 1)
  in
  List.iter (fun cl -> List.iter (count t) cl) l;
  let best_score = ref 0 in
  let best_atom = ref efalse in
  let check_best a c =
    if !c > !best_score then begin
      best_score := !c;
      best_atom := a;
    end;
  in
  HE.iter check_best t;
  if l = [] then enot (efalse)
  else if !best_score = 0 then efalse
  else begin
    let (haves, havenots) = List.partition (element !best_atom) l in
    let nhaves = List.map (remove !best_atom) haves in
    mkand (mkor !best_atom (factor_clauses nhaves)) (factor_clauses havenots)
  end
;;

let is_upper s = s <> "" && s.[0] >= 'A' && s.[0] <= 'Z';;

let rec get_vars accu e =
  match e with
  | Evar (v, _) when is_upper v -> if List.mem v accu then accu else v :: accu
  | Evar _ -> accu
  | Emeta _ -> assert false
  | Eapp (s, args, _) -> List.fold_left get_vars accu args
  | Enot (f, _) -> get_vars accu f
  | Eand (f, g, _) -> get_vars (get_vars accu f) g
  | Eor (f, g, _) -> get_vars (get_vars accu f) g
  | Eimply (f, g, _) -> get_vars (get_vars accu f) g
  | Eequiv (f, g, _) -> get_vars (get_vars accu f) g
  | Etrue -> accu
  | Efalse -> accu
  | Eall _ -> assert false
  | Eex _ -> assert false
  | Etau _ -> assert false
;;

let add_quants vars e =
  List.fold_left (fun e v -> eall (v, "", e)) e vars
;;

let rec remove l1 l2 =
  match l2 with
  | [] -> []
  | h::t -> if List.mem h l1 then remove l1 t else h :: (remove l1 t)
;;

let rec inter l1 l2 = List.filter (fun x -> List.mem x l1) l2;;

let rec generalise ctx e =
  match e with
  | Evar _ -> e
  | Emeta _ -> assert false
  | Eapp (s, args, _) -> add_quants (remove ctx (get_vars [] e)) e
  | Enot (Efalse, _) -> e
  | Enot (f, _) -> add_quants (remove ctx (get_vars [] f)) e
  | Eand (f, g, _) -> generalise_pair ctx eand f g
  | Eor (f, g, _) -> generalise_pair ctx eor f g
  | Eimply (f, g, _) -> generalise_pair ctx eimply f g
  | Eequiv (f, g, _) -> generalise_pair ctx eequiv f g
  | Etrue -> e
  | Efalse -> e
  | Eall _ -> assert false
  | Eex _ -> assert false
  | Etau _ -> assert false

and generalise_pair ctx op e f =
  let ve = get_vars [] e and vf = get_vars [] f in
  let local = remove ctx (inter ve vf) in
  let newctx = local @ ctx in
  let ee = generalise newctx e in
  let ff = generalise newctx f in
  add_quants local (op (ee, ff))
;;

let translate dir ps =
  clauses := [];
  let forms = trans dir ps in
  let hyps =
        if !clauses <> [] then
          (generalise [] (factor_clauses !clauses), 0) :: forms
        else
          forms
  in
  List.map (fun (e, p) -> Phrase.Hyp (e, p)) hyps
;;
