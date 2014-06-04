
open Expr
open Mlproof

let equal x y = Expr.compare x y = 0

(* Types manipulation *)
let get_type = function
    | Etrue | Efalse -> "$o"
    | Etau (_, t, _, _)
    | Emeta(Eall(_, t, _, _), _)
    | Emeta(Eex(_, t, _, _), _) -> t
    | e -> begin match priv_type e with
        | None -> Namespace.univ_name
        | Some s -> s
    end

let is_int e = get_type e = "$int"
let is_rat e = get_type e = "$rat"

let ctype t t' = match t, t' with
    | "$int", "$int" -> "$int"
    | "$int", "$rat" | "$rat", "$int" | "$rat", "$rat" -> "$rat"
    | _ -> "$real"
let etype e e' = ctype (get_type e) (get_type e')

(* Manipulation of expressions/formulas *)
exception NotaFormula

let is_z v = Z.equal (Q.den v) Z.one
let is_q v = not (Z.equal (Q.den v) Z.zero || is_z v)
let floor v =
    try
         Q.of_bigint (Z.ediv (Q.num v) (Q.den v))
    with Division_by_zero -> v
let ceil v = Q.neg (floor (Q.neg v))

let comp_neg = function
    | "$less" -> "$greatereq"
    | "$lesseq" -> "$greater"
    | "$greater" -> "$lesseq"
    | "$greatereq" -> "$less"
    | "$is_int" -> "$not_is_int"
    | "$is_rat" -> "$not_is_rat"
    | _ -> assert false

(* Combine types *)
let mk_app t s l = add_type t (eapp (s, l))

let const s =
    if is_z (Q.of_string s) then
        mk_app "$int" s []
    else
        mk_app "$rat" s []

let sum a b = mk_app (etype a b) "$sum" [a; b]
let diff a b = mk_app (etype a b) "$difference" [a; b]
let uminus a = mk_app (get_type a) "$uminus" [a]
let mul a b = mk_app (etype a b) "$product" [a; b]
let minus_one e = mk_app (get_type e) "$difference" [e; const "1"]
let plus_one e = mk_app (get_type e) "$sum" [e; const "1"]

let eeq a b = mk_app "$o" "$eq_num" [a; b]
let less a b = mk_app "$o" "$less" [a; b]
let lesseq a b = mk_app "$o" "$lesseq" [a; b]
let greater a b = mk_app "$o" "$greater" [a; b]
let greatereq a b = mk_app "$o" "$greatereq" [a; b]

let rec find_coef x = function
    | [] -> raise Not_found
    | (c, y) :: r -> if equal x y then c else find_coef x r

let rec fadd_aux (c, x) = function
    | [] -> [(c, x)]
    | (c', y) :: r ->
            if equal x y then
                (Q.add c c', x) :: r
            else
                (c', y) :: (fadd_aux (c, x) r)

let fadd a b = List.fold_left (fun e c -> fadd_aux c e) a b
let fdiff a b = fadd a (List.map (fun (c, x) -> (Q.neg c, x)) b)
let fmul c a = List.map (fun (c', x) -> (Q.mul c c', x)) a

let fis_int = List.for_all (fun (_, e) -> is_int e)
let fis_tau = List.for_all (fun (_, e) -> match e with Emeta(_) -> false | _ -> true)
let fis_meta = List.for_all (fun (_, e) -> match e with Emeta(_) -> true | _ -> false)

let fneg (b, s, c) =
    let s = comp_neg s in
    if not (fis_int b) then
        (b, s, c)
    else begin match s with
    | "$less" -> (b, "$lesseq", Q.sub c Q.one)
    | "$greater" -> (b, "$greatereq", Q.add c Q.one)
    | _ -> (b, s, c)
    end

let rec sanitize = function
    | [] -> []
    | (c, _) as a :: r -> if Q.equal Q.zero c then (sanitize r) else a :: (sanitize r)

let normalize a b =
    let rec pop_const = function
        | [] -> (Q.zero, [])
        | (c, x) :: r ->
                if equal etrue x then
                    (Q.neg c), r
                else
                    let c', r' = pop_const r in
                    c', (c, x) :: r'
    in
    let coef e =
        if e = [] then
            Q.one
        else
            let k = Q.of_bigint (List.fold_left (fun k c -> if Q.is_real c then Z.lcm k (Q.den c) else k) Z.one e) in
            let aux = (fun g c -> Z.gcd g (Q.to_bigint (Q.mul c k))) in
            Q.div k (Q.of_bigint (List.fold_left aux (Q.to_bigint (Q.mul (List.hd e) k)) (List.tl e)))
    in
    let f = fdiff a b in
    let c, e = pop_const f in
    let e = sanitize e in
    let k = Q.abs (coef (List.map fst e)) in
    Q.mul c k, (List.map (fun (c, x) -> (Q.mul c k, x)) e)

let of_cexpr e = match e with
    | Eapp (s, [], _) when is_int e || is_rat e ->
            begin try
                Q.of_string s
            with Invalid_argument _ ->
                raise Exit
            end
    | _ -> raise NotaFormula

let rec of_nexpr = function
    | Eapp (v, [], _) as e ->
        begin try [of_cexpr e, etrue] with Exit -> [Q.one, e] end
    | Evar (v, _) as a when is_int a || is_rat a -> [Q.one, a]
    | Emeta (Eall(_, ("$int"|"$rat"), _, _), _) as a -> [Q.one, a]
    | Emeta (Eex(_, ("$int"|"$rat"), _, _), _) as a -> [Q.one, a]
    | Etau (_, ("$int"|"$rat"), _, _) as a -> [Q.one, a]
    | Eapp ("$uminus", [a], _) -> fdiff [Q.zero, etrue] (of_nexpr a)
    | Eapp ("$sum", [a; b], _) -> fadd (of_nexpr a) (of_nexpr b)
    | Eapp ("$difference", [a; b], _) -> fdiff (of_nexpr a) (of_nexpr b)
    | Eapp ("$product", [Eapp (_, [], _) as e; a], _)
    | Eapp ("$product", [a; Eapp (_, [], _) as e], _) ->
            begin try
                fmul (of_cexpr e) (of_nexpr a)
            with Exit ->
                raise NotaFormula
            end
    | _ -> raise NotaFormula

let of_bexpr = function
    | Eapp (("$less"|"$lesseq"|"$greater"|"$greatereq"|"$eq_num") as s, [a; b], _ ) ->
            let a', b' = of_nexpr a, of_nexpr b in
            let c, e = normalize a' b' in
            (e, s, c)
    | Eapp (("$is_int"|"$is_rat"|"$not_is_int"|"$not_is_rat") as s, [a], _) ->
            let a' = of_nexpr a in
            let c, e = normalize [Q.zero, etrue] a' in
            (e, s, c)
    | _ -> raise NotaFormula

let to_nexpr_aux (c, x) = if Q.equal Q.one c then x else mul (const (Q.to_string c)) x

let to_nexpr = function
    | [] -> const "0"
    | (c, x) :: r -> List.fold_left
        (fun e (c', x') -> if Q.sign c' < 0 then diff e (to_nexpr_aux (Q.neg c', x')) else sum e (to_nexpr_aux (c', x')))
                          (if Q.sign c < 0 then uminus (to_nexpr_aux (Q.neg c, x)) else to_nexpr_aux (c, x)) r

let to_bexpr (e, s, c) = mk_app "$o" s [to_nexpr e; const (Q.to_string c)]

let expr_norm e = try to_bexpr (of_bexpr e) with NotaFormula -> e

(* Aanalog to circular lists with a 'stop' element, imperative style *)
exception EndReached

type 'a clist = {
    mutable front : 'a list;
    mutable acc : 'a list;
}

let cl_is_empty l = l.front = [] && l.acc = []

let cl_to_list l = (List.rev l.acc) @ l.front

let cl_from_list l = {
    front = l;
    acc = []
}

let cl_current l =
    if l.front = [] then
        raise EndReached
    else
        List.hd l.front

let cl_next l =
    if l.front = [] then
        raise EndReached
    else begin
        let x = List.hd l.front in
        l.front <- List.tl l.front;
        l.acc <- x :: l.acc
    end

let cl_reset l =
    (* l.front *should* be empty, but just in case,.. *)
    l.front <- (List.rev l.acc) @ l.front;
    l.acc <- []

(* Combinatorial tree *)
type 'a ctree = {
    node : 'a clist;
    children : 'a ctree array;
}

let ct_is_empty t =
    Array.length t.children = 0 && cl_is_empty t.node

let cl_to_list l = (List.rev l.acc) @ l.front

let rec reset t =
    cl_reset t.node;
    Array.iter reset t.children

let rec next t =
    try
        cl_next t.node
    with EndReached ->
        if Array.length t.children = 0 then
            raise EndReached
        else begin
            let i = ref 0 in
            try
                while true do
                    if !i >= Array.length t.children then
                        raise EndReached;
                    try
                        next t.children.(!i);
                        raise Exit
                    with EndReached ->
                        reset t.children.(!i);
                        incr i
                done
            with Exit -> ()
        end

let rec current t =
    let rec aux t =
        try
            [cl_current t.node]
        with EndReached ->
            if Array.length t.children = 0 then
                raise Exit
            else
                List.concat @@ Array.to_list @@ (Array.map aux t.children)
    in
    try
        aux t
    with Exit ->
        next t; current t

let ct_all t =
    let res = ref [] in
    try
        while true do
            res := (current t) :: !res;
            next t
        done;
        !res
    with EndReached -> List.rev !res

let is_inst_node p = match p.mlrule with
    | All (e, e') -> begin match e' with
        | Emeta(e'', _) when equal e e'' -> false
        | _ -> true
        end
    | NotEx(e, e') -> begin match e' with
        | Emeta(e'',_) when equal e (Type.bnot e'') ||  equal e (enot e'') -> false
        | _ -> true
        end
    | _ -> false

let expr_of_inst p = match p.mlrule with
    | All (e, _) | NotEx(e, _) -> e
    | _ -> assert false

let ct_from_ml p =
    let filter l = List.filter (fun e ->
        try begin match of_bexpr e with
            | (_, "$eq_num", _) -> false
            | (f, _, _) -> fis_meta f
        end with NotaFormula -> false
        ) l in
    let rec aux p =
        if is_inst_node p then
            { node = cl_from_list []; children = [| |]; }
        else
            let ehyps = Array.fold_left (fun acc p -> p.mlconc @ acc) [] p.mlhyps in
            let hyps = Array.to_list p.mlhyps in
            let hyps = List.filter is_open_proof hyps in
            let hyps = List.map aux hyps in
            let hyps = List.filter (fun t -> not (ct_is_empty t)) hyps in
            let hyps = Array.of_list hyps in
            {
                node = cl_from_list (filter (Expr.diff p.mlconc ehyps));
                children = hyps;
            }
    in
    let res = aux p in
    if ct_is_empty res then
        None
    else
        Some res

exception Found_inst of proof
let find_next_inst p =
    let rec aux p =
        if is_inst_node p
        then raise (Found_inst p)
        else Array.iter aux p.mlhyps
    in
    try aux p; raise EndReached with Found_inst p -> { p with mlrule =
        Ext("arith", "inst", match p.mlrule with
            | All(e, e') -> [e; e']
            | NotEx(e, e') -> [e; e']
            | _ -> assert false) }

let replace_inst p inst =
    let e = expr_of_inst inst in
    let rec aux p = match p.mlrule with
        | All(e', _) when equal e e' -> inst
        | NotEx(e', _) when equal e e' -> inst
        | _ -> { p with mlhyps = Array.map aux p.mlhyps }
    in
    aux p

let next_inst p = replace_inst p (find_next_inst p)


(* Simplex solver with a cache *)
let lhash l = List.fold_left (+) 0 (List.map Expr.hash l)
let lequal l l' = try List.for_all2 equal l l' with Invalid_argument _ -> false

module Simplex = Simplex.MakeHelp(struct type t = Expr.t let compare = Expr.compare end)
module ElH = Hashtbl.Make(struct type t = Expr.t list let hash = lhash let equal = lequal end)

let cache = ElH.create 97

let simplex_is_int = function
    | Simplex.Extern v -> is_int v
    | Simplex.Intern _ -> false

let simplex_is_var = function
    | Simplex.Extern v -> true
    | Simplex.Intern _ -> false

let simplex_var = function
    | Simplex.Extern v -> v
    | Simplex.Intern _ -> assert false

let add_expr e st =
    try match fneg (of_bexpr e) with
    | (b, "$lesseq", c) -> Simplex.add_constraints st [Simplex.LessEq, b, c]
    | (b, "$greatereq", c) -> Simplex.add_constraints st [Simplex.GreaterEq, b, c]
    | (b, "$eq_num", c) -> Simplex.add_constraints st [Simplex.Eq, b, c]
    | _ -> st
    with
    | NotaFormula -> assert false

let rec get_state l =
    try
        ElH.find cache l
    with Not_found ->
        begin match l with
        | [] -> Some(Simplex.empty, fun () -> None)
        | e :: r ->
                let res = match get_state r with
                | None -> None
                | Some(st, _) ->
                    let st = add_expr e st in
                    try
                        let f = Simplex.nsolve_incr st simplex_is_int in
                        begin match f () with
                        | None -> Some(st, f)
                        | Some Simplex.Solution _ -> Some(st, f)
                        | Some Simplex.Unsatisfiable _ -> None
                        end
                    with Invalid_argument "Simplex is empty." -> None
                in
                ElH.add cache l res;
                res
        end

let try_solve l =
    match get_state l with
    | None -> None
    | Some (_, f) -> begin match f () with
        | None -> None
        | Some Simplex.Unsatisfiable _ -> None
        | Some Simplex.Solution s ->
                Some (List.map (fun (v, x) -> (simplex_var v, x)) (List.filter (fun (v, _) -> simplex_is_var v) s))
        end

let solve_tree t =
    reset t;
    let rec aux () =
        match try_solve (current t) with
        | Some s -> Some s
        | None ->
                try
                    next t;
                    aux ()
                with EndReached -> None
    in
    aux ()
