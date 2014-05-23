
(* TODO:
 * - Use formula number (from index) instead of storing them.
*)

open Expr
open Node
open Mlproof
module M = Map.Make(struct type t= Expr.t let compare = Expr.compare end)
module S = Simplex.Make(struct type t = Expr.t let compare = Expr.compare end)


(* Expression/Types manipulation *)
let equal x y = Expr.compare x y = 0

let get_type = function
    | Etrue | Efalse -> "$o"
    | Etau (_, t, _, _) -> t
    | e -> begin match priv_type e with
        | None -> Namespace.univ_name
        | Some s -> s
    end

let is_int e = get_type e = "$int"
let is_rat e = get_type e = "$rat"

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
let ctype t t' = match t, t' with
    | "$int", "$int" -> "$int"
    | "$int", "$rat" | "$rat", "$int" | "$rat", "$rat" -> "$rat"
    | _ -> "$real"
let etype e e' = ctype (get_type e) (get_type e')

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

(* Nodes generated by the extension *)

let mk_node_const s c e g = (* e is a trivially false comparison of constants *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "const_" ^ s, [const (Q.to_string c)]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| |];
    }

let mk_node_eq a b e g = (* e : a = b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "eq", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (lesseq a b); expr_norm (greatereq a b)] |];
    }

let mk_node_neq a b e g = (* e : a != b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neq", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (less a b)]; [expr_norm (greater a b)] |];
    }

let mk_node_tighten s x c e g =
    Node {
        nconc = [e];
        nrule = Ext ("arith", "tighten_" ^ s, [x; const c]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_app "$o" s [x; const c]] |];
    }

let mk_node_var e1 e2 e g = (* e1 : v = expr, e2 : v {comp} const, e : expr {comp} const *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "var", [e1; e2]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e1; e2] |];
    }

let mk_node_neg s a e g = (* e : ~ {s} b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neg_" ^ s, [a]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_app "$o" (comp_neg s) [a] ] |];
    }

let mk_node_neg2 s a b e g = (* e : ~ a {s} b *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "neg_" ^ s, [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [mk_app "$o" (comp_neg s) [a; b] ] |];
    }

let mk_node_int_lt a b e g = (* e : a < b, => a <= b - 1 *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "int_lt", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (lesseq a (minus_one b))] |];
    }

let mk_node_int_gt a b e g = (* e : a > b, => a >= b + 1 *)
    Node {
        nconc = [e];
        nrule = Ext ("arith", "int_gt", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [expr_norm (greatereq a (plus_one b))] |];
    }

let mk_node_branch v e e' g =
    Node {
        nconc = [];
        nrule = Ext ("arith", "simplex_branch", [e; e']);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e]; [e']; |];
    }

let mk_node_lin x e l g =
    Node {
        nconc = l;
        nrule = Ext ("arith", "simplex_lin", e :: l);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [e] |];
    }

let mk_node_sim e b res g =
    Node {
        nconc = e :: b;
        nrule = Ext("arith", "simplex_bound", e :: b);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [res] |];
    }

let mk_node_conflict e e' g =
    Node {
        nconc = [e; e'];
        nrule = Ext("arith", "conflict", [e; e']);
        nprio = Prop;
        ngoal = g;
        nbranches = [| |];
    }

(* Helper around the simplex module *)
type simplex_state = {
    core : S.t;
    ignore : expr list;
    bindings : (expr * expr * expr option * expr option) list;
}

let simplex_empty = {
    core = S.empty;
    ignore = [];
    bindings = [];
}

let bounds_of_comp s c = match s with
    | "$lesseq" -> (Q.minus_inf, c)
    | "$greatereq" -> (c, Q.inf)
    | _ -> (Q.minus_inf, Q.inf)

let low_binding c' c d' d f low high =
    if Q.gt (Q.div c' c) (Q.div d' d) then
        f, high
    else
        low, high

let high_binding c' c d' d f low high =
    if Q.lt (Q.div c' c) (Q.div d' d) then
        low, f
    else
        low, high

let new_bindings low high f = function
    | [c, x], "$lesseq", c' ->
            if Q.sign c <= -1 then begin match low with
                | None -> f, high
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$greatereq", d' when Q.sign d >= 0 ->
                                low_binding c' c d' d f low high
                        | [d, y], "$lesseq", d' when Q.sign d <= -1 ->
                                low_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end else begin match high with
                | None -> low, f
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$lesseq", d' when Q.sign d >= 0 ->
                                high_binding c' c d' d f low high
                        | [d, y], "$greatereq", d' when Q.sign d <= -1 ->
                                high_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end
    | [c, x], "$greatereq", c' ->
            if Q.sign c >= 0 then begin match low with
                | None -> f, high
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$greatereq", d' when Q.sign d >= 0 ->
                                low_binding c' c d' d f low high
                        | [d, y], "$lesseq", d' when Q.sign d <= -1 ->
                                low_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end else begin match high with
                | None -> low, f
                | Some expr -> begin match (of_bexpr expr) with
                        | [d, y], "$lesseq", d' when Q.sign d >= 0 ->
                                high_binding c' c d' d f low high
                        | [d, y], "$greatereq", d' when Q.sign d <= -1 ->
                                high_binding c' c d' d f low high
                        | _ -> assert false
                        end
            end
    | _ -> low, high

let print_opt fmt = function
    | None -> Format.fprintf fmt "empty"
    | Some e -> Type.print_expr fmt e

let print_binding fmt (x, def, inf, upp) =
    Format.fprintf fmt "%a -:- %a@\nInf :%a@\nUpp :%a@]@."
    Type.print_expr x Type.print_expr def
    print_opt inf print_opt upp

let print_bindings fmt = List.iter (print_binding fmt)

let translate_bound e r = match e with
    | None -> r ()
    | Some e -> begin match (of_bexpr e) with
        | [c, x], _, c' -> Q.div c' c
        | _ -> assert false
    end

let pop_option = function | Some a -> a | None -> assert false

let bound_of_expr is_high e bounds =
    let xor a b = (a && not b) || (not a && b) in
    let rec aux = function
        | [] -> raise Exit
        | [c, x] ->
                let v, _, einf, eupp = List.find (fun (y, _, _, _) -> equal x y) bounds in
                if xor is_high (Q.sign c >= 0) then begin
                    [pop_option einf], Q.mul c (translate_bound einf (fun () -> raise Exit))
                end else begin
                    [pop_option eupp], Q.mul c (translate_bound eupp (fun () -> raise Exit))
                end
        | (c, x) :: r ->
                let l, b = aux r in
                let _, _, einf, eupp = List.find (fun (y, _, _, _) -> equal x y) bounds in
                if xor is_high (Q.sign c >= 0) then
                    (pop_option einf) :: l, Q.add b (Q.mul c (translate_bound einf (fun () -> raise Exit)))
                else
                    (pop_option eupp) :: l, Q.add b (Q.mul c (translate_bound eupp (fun () -> raise Exit)))
    in
    try aux e with Exit -> [], if is_high then Q.inf else Q.minus_inf


let bounds_of_clin v expr bounds =
    let expr = sanitize expr in
    let _, _, einf, eupp = List.find (fun (y, _, _, _) -> equal y v) bounds in
    let inf = translate_bound einf (fun () -> Q.minus_inf) in
    let upp = translate_bound eupp (fun () -> Q.inf) in
    let l_bounds, low = bound_of_expr false expr bounds in
    let h_bounds, high = bound_of_expr true expr bounds in
    if Q.gt low upp then
        l_bounds, greatereq v (const (Q.to_string low)), pop_option eupp
    else if Q.lt high inf then
        h_bounds, lesseq v (const (Q.to_string high)), pop_option einf
    else if Q.gt inf upp then
        [], pop_option einf, pop_option eupp
    else begin
        (* Format.printf "Bindings (%i):@\n%a@\n---------------@.%s <= %s@\n%a@\n%a@."
        (List.length bounds) print_bindings bounds
        (Q.to_string low) (Q.to_string high)
        Type.print_expr v Type.print_expr (to_nexpr expr); *)
        assert false
    end

let add_binding t x f (e, s, c) =
    let l1, l2 = List.partition (fun (y, _, _, _) -> equal x y) t.bindings in
    let _, def, low, high =
        if List.length l1 = 0 then begin x, x, None, None end
        else if List.length l1 = 1 then begin List.hd l1 end
        else assert false in
    let low, high = new_bindings low high (Some f) (e, s, c) in
    { t with bindings = (x, def, low, high) :: l2 }

let simplex_add t f (e, s, c) = match e with
    | []  -> assert false
    | [(c', x)] ->
            let b = Q.div c (Q.abs c') in
            let (inf, upp) = bounds_of_comp s b in
            let (inf, upp) = if Q.sign c' <= -1 then (Q.neg upp, Q.neg inf) else (inf, upp) in
            (* Format.printf "Bindings : @\n%a@\n-----------@." print_bindings t.bindings; *)
            (add_binding {t with core = S.add_bounds t.core (x, inf, upp)} x f (e, s, c)), []
    | _ ->
            let expr = to_nexpr e in
            let v = add_type (get_type expr) (newvar ()) in
            let e1 = eeq v expr in
            let e2 = mk_app "$o" s [v; const (Q.to_string c)] in
            { core = S.add_eq t.core (v, e);
              ignore = e1 :: t.ignore;
              bindings = (v, e1, None, None) :: t.bindings;
            }, [f, mk_node_var e2 e1 f] (* The order (e2 before e1) is actually VERY important here !! *)

exception Internal_error
let nodes_of_tree s f t =
    let rec aux s f t = match !t with
    | None -> raise Internal_error
    | Some S.Branch (v, k, c, c') ->
            let k = const (Z.to_string k) in
            let under = expr_norm (lesseq v k) in
            let above = expr_norm (greatereq v (plus_one k)) in
            (f, mk_node_branch v under above) :: (
                (aux (add_binding s v under (of_bexpr under)) under c) @
                (aux (add_binding s v above (of_bexpr above)) above c'))
    | Some S.Explanation (v, expr) ->
            let expr = sanitize expr in
            let l = v :: (List.map snd expr) in
            let relevant = List.map (fun (_, z, _, _) -> z)
                (List.filter (fun (y, y', _, _) -> not (equal y y') && List.exists (fun x -> equal x y) l) s.bindings) in
            let clin = expr_norm (mk_app "$o" "$eq_num" [to_nexpr expr; v]) in
            let bounds, nb, conflict = bounds_of_clin v expr s.bindings in
            if bounds = [] then
                [f, mk_node_conflict nb conflict]
            else
                [f, mk_node_lin v clin relevant;
                 clin, mk_node_sim clin bounds nb;
                 nb, mk_node_conflict nb conflict]
    in
    aux s f t

let simplex_solve s e =
    let res = S.nsolve s.core is_int in
    match res with
    | S.Solution _ -> false, []
    | S.Unsatisfiable cert -> true, nodes_of_tree s e cert


(* Internal state *)
type state = {
    mutable solved : bool;
    stack : (expr * simplex_state * ((expr * (int -> Node.node_item)) list)) Stack.t;
}

let empty_state = {
    solved = false;
    stack = Stack.create ();
}

let st_solved st = st.solved <- true

let st_pop st =
    ignore (Stack.pop st.stack);
    st.solved <- false

let st_head st =
    try
        let _, r, _ = Stack.top st.stack in
        r
    with Stack.Empty -> simplex_empty

let st_push st x = Stack.push x st.stack

let st_is_head st e =
    try
        let e', _, _ = Stack.top st.stack in
        equal e e'
    with Stack.Empty -> false

(* Extension functions *)
exception Found of (int -> node_item)

let is_coherent e = function
    | Stop -> assert false
    | Node n -> List.for_all (fun e' -> equal e e' || Index.member e') n.nconc

let ignore_expr, add_expr, remove_expr, todo, add_todo =
    let st = empty_state in
    let is_new e =
        try Stack.iter (fun (e', _, l) ->
            if (List.exists (fun (e', _) -> equal e e') l) then raise Exit) st.stack;
        true
        with Exit -> false

    and ignore_expr e =
        try
            Stack.iter (fun (_, t, l) ->
                if List.exists (equal e) t.ignore then raise Exit;
                if List.exists (fun (y, _) -> equal e y) l then raise Exit)
            st.stack;
            false
        with Exit -> true
    in

    let add e = (* try and compute a solution *)
        if is_new e && not st.solved && not (ignore_expr e) then begin
            try
                let (f, s, c) = of_bexpr e in
                let t = st_head st in
                if f <> [] then begin
                    let t', res = simplex_add t e (f, s, c) in
                    let b, res' = simplex_solve t' e in
                    let res'' = res @ res' in
                    st_push st (e, t', res'');
                    if b then st_solved st
                end
            with NotaFormula -> ()
        end
    in

    let rec remove e = if st_is_head st e then begin st_pop st; remove e end in

    let add_todo e n = st_push st (e, (st_head st), List.map (fun m -> e, m) n)

    and todo e g =
        let res = ref [] in
        Stack.iter (fun (_,_,l) -> List.iter (fun (e', n) ->
            if equal e e' then res := (n g) :: !res) l) st.stack;
        List.filter (is_coherent e) !res
    in
    ignore_expr, add, remove, todo, add_todo

(* Fourier-Motzkin *)
type fm_state = (Expr.t list * Expr.t list) M.t

let fm_empty = M.empty

let fm_get st x = try M.find x st with Not_found -> [], []

let fm_lower s c = match s with
    | "$less" | "$lesseq" -> Q.sign c < 0
    | "$greater" | "$greatereq" -> Q.sign c > 0
    | _ -> assert false

let fm_deduce_aux x e f =
    let (be, se, ce) = of_bexpr e in
    let (bf, sf, cf) = of_bexpr f in
    let cex = find_coef x be in
    let cfx = find_coef x bf in
    match se, sf with
    | "$less", "$less" | "$lesseq", "$less" | "$less", "$lesseq" ->
            assert (Q.sign cex < 0 && Q.sign cfx > 0);
            let t = fdiff
                (fmul cfx (fdiff be [(cex, x);(ce, etrue)]))
                (fmul cex (fdiff bf [(cfx, x);(cf, etrue)])) in
            let g = expr_norm (less t (const "0")) in
            mk_node_fm e f g
    | "$lesseq","$lesseq" ->
            assert (Q.sign cex < 0 && Q.sign cfx > 0);
            let t = fdiff
                (fmul cfx (fdiff be [cex, x;ce, etrue]))
                (fmul cex (fdiff bf [cfx, x;cf, etrue])) in
            let g = expr_norm (lesseq t (const "0")) in
            mk_node_fm e f g
    | "$greater", "$greater" ->
            assert (Q.sign cex > 0 && Q.sign cfx < 0);
            let t = fdiff
                (fmul cfx (fdiff be [cex, x; ce, etrue]))
                (fmul cfx (fdiff be [cex, x; ce, etrue])) in
            let g = expr_norm (less t (const "0")) in
            mk_node_fm e f g


let fm_deduce1 x e l = List.concat (List.map (fm_deduce_aux x e) l)
let fm_deduce2 x e l = List.concat (List.map (fun e' -> fm_deduce_aux x e' e) l)

let fm_add_aux st (s, c, x) e =
    if fm_lower s c then
        let low, high = fm_get st x in
        let res = fm_deduce1 x e high in
        M.add x (e :: low, high) st, res
    else
        let low, high = fm_get st x in
        let res = fm_deduce2 x e low in
        M.add x (low, e :: high) st, res

let fm_add st e =
    let (b, s, _) = of_bexpr e in
    let aux (acc, l) (c, x) =
        let st', l' = fm_add_aux st (s, c, x) e in
        (st', (l @ l'))
    in
    List.fold_left aux (st, []) b

let fm_add_expr, fm_rm_expr =
    let st = ref fm_empty in
    let add e = match e with
        | Eapp (("$less"|"$lesseq"|"$greater"|"$greatereq"), [a; b], _) when is_rat a && is_rat b ->
                begin try
                    let st', res = fm_add !st e in
                    add_todo e res;
                    st := st'
                with NotaFormula -> () end
        | _ -> ()
    in
    let rm e =
        st := M.map (fun (l, l') ->
            List.filter (fun e'' -> not (equal e e'')) l,
            List.filter (fun e'' -> not (equal e e'')) l') !st
    in
    add, rm


(* Constants *)
let const_node e = (* comparison of constants *)
    let (f, s, c) = of_bexpr e in
    assert (f = []);
    begin match s with
    | "$less" when Q.geq Q.zero c -> add_todo e [mk_node_const "lt" c e]
    | "$lesseq" when Q.gt Q.zero c -> add_todo e [mk_node_const "leq" c e]
    | "$greater" when Q.leq Q.zero c -> add_todo e [mk_node_const "gt" c e]
    | "$greatereq" when Q.lt Q.zero c -> add_todo e [mk_node_const "geq" c e]
    | "$eq_num" when not (Q.equal Q.zero c) -> add_todo e [mk_node_const "eq" c e]
    | "$is_int" when not (is_z c) -> add_todo e [mk_node_const "is_int" c e]
    | "$not_is_int" when is_z c -> add_todo e [mk_node_const "not_int" c e]
    | "$not_is_rat" -> add_todo e [mk_node_const "not_rat" c e]
    | _ -> ()
    end

let is_const e = try let (f, _, _) = of_bexpr e in f = [] with NotaFormula -> false

(* Adding formulas *)
let add_formula e =
    fm_add_expr e;
    match e with
    | _ when ignore_expr e -> ()
    | Enot (Eapp ("$eq_num", [a; b], _), _) ->
            add_todo e [mk_node_neq a b e]
    | Enot (Eapp (("$less"|"$lesseq"|"$greater"|"$greatereq") as s, [a; b], _), _) ->
            add_todo e [mk_node_neg2 s a b e]
    | Enot (Eapp (("$is_int"|"$is_rat") as s, [a], _), _) ->
            add_todo e [mk_node_neg s a e]
    | _ when is_const e ->
            const_node e
    | Eapp ("$eq_num", [a; b], _) ->
            add_todo e [mk_node_eq a b e]
    | Eapp ("$less", [a; b], _) when is_int a && is_int b ->
            add_todo e [mk_node_int_lt a b e]
    | Eapp ("$greater", [a; b], _) when is_int a && is_int b ->
            add_todo e [mk_node_int_gt a b e]
    | _ -> begin try
            begin match (of_bexpr e) with
            | [(c', x)], ("$less"|"$lesseq"), c when is_int x && is_q (Q.div c c') ->
                    let c'' = Q.div c c' in
                    if Q.sign c' <= -1 then
                        add_todo e [mk_node_tighten "$greatereq" x (Q.to_string (ceil c'')) e]
                    else
                        add_todo e [mk_node_tighten "$lesseq" x (Q.to_string (floor c'')) e]
            | [(c', x)], ("$greater"|"$greatereq"), c when is_int x && is_q (Q.div c c') ->
                    let c'' = Q.div c c' in
                    if Q.sign c' <= -1 then
                        add_todo e [mk_node_tighten "$lesseq" x (Q.to_string (floor c'')) e]
                    else
                        add_todo e [mk_node_tighten "$greatereq" x (Q.to_string (ceil c'')) e]
            | _ -> add_expr e
            end with
            | NotaFormula -> ()
    end

let remove_formula e =
    remove_expr e;
    fm_rm_expr e

let newnodes e g _ = todo e g

let make_inst term g = assert false

let to_llproof f p t = t.(0)

let declare_context_coq fmt = ()

let p_rule_coq fmt r = ()

let predef () = []
;;

Extension.register {
  Extension.name = "arith";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = (fun x -> x);
  Extension.add_phrase = (fun _ -> ());
  Extension.postprocess = (fun x -> x);
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;

