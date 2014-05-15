
(* TODO:
 * - finish wrapper function aroun ssimplex
 * - put equations in normal form whenever we encounter one (mainly the ones we add in a node)
*)

open Expr
open Node
open Mlproof
module S = Simplex.Make(struct type t = Expr.t let compare = Expr.compare end)

(* Manipulation of expressions/formulas *)
exception NotaFormula

let const s = eapp ("$int", [evar s])
let sum a b = eapp ("$sum", [a; b])
let mul a b = eapp ("$product", [a; b])

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

let normalize a b =
    let rec sanitize = function
        | [] -> []
        | (c, _) as a :: r -> if Q.equal Q.zero c then r else a :: (sanitize r)
    in
    let rec pop_const = function
        | [] -> (Q.zero, [])
        | (c, x) :: r ->
                if equal etrue x then
                    c, r
                else
                    let c', r' = pop_const r in
                    c', (c, x) :: r'
    in
    let c = fdiff a b in
    pop_const (sanitize c)

let of_cexpr = function
    | Evar (s, _) -> Q.of_string s
    | _ -> raise NotaFormula

let rec of_nexpr = function
    | Eapp (("$int"|"$rat"), [v], _) -> [of_cexpr v, etrue]
    | Etau (_, ("$int"|"$rat"), _, _) as a -> [Q.one, a]
    | Eapp ("$sum", [a; b], _) -> fadd (of_nexpr a) (of_nexpr b)
    | Eapp ("$difference", [a; b], _) -> fdiff (of_nexpr a) (of_nexpr b)
    | Eapp ("product", [Eapp (("$int"|"$rat"), [v], _); a], _)
    | Eapp ("product", [a; Eapp (("$int"|"$rat"), [v], _)], _) ->
            fmul (of_cexpr v) (of_nexpr a)
    | _ -> raise NotaFormula

let of_bexpr = function
    | Eapp (("$lesseq"|"$greatereq"|"$eq_$int"|"$eq_$rat") as s, [a; b], _ ) ->
            let a', b' = of_nexpr a, of_nexpr b in
            let e, c = normalize a' b' in
            (e, s, c)
    | _ -> raise NotaFormula

let to_nexpr = function
    | [] -> const "0"
    | (c, x) :: r -> List.fold_left (fun e (c', x') -> sum e (mul (const (Q.to_string c')) x')) (mul (const (Q.to_string c)) x) r

let to_bexpr (e, s, c) = eapp (s, [to_nexpr e; const c])

(* Helper around the simplex module *)
type simplex = {
    core : S.t;
    bindings : (expr * expr) list;
}

let simplex_empty = {
    core = S.empty;
    bindings = [];
}

let simplex_add s f =
    s

let simplex_solve s =
    false, []

(* Internal state *)
type state = {
    mutable solved : bool;
    stack : (expr * simplex) Stack.t;
    mutable todo : (expr * Node.node_item) list; (* could be a map ? *)
}

let empty_state = {
    solved = false;
    stack = Stack.create ();
    todo = [];
}

let st_pop st =
    ignore (Stack.pop st.stack);
    st.solved <- false;
    st.todo <- []

let st_head st =
    try
        snd (Stack.top st.stack)
    with Stack.Empty -> simplex_empty

let st_push st x = Stack.push x st.stack

let st_is_head st e =
    try
        let e', _ = Stack.top st.stack in
        equal e e'
    with Stack.Empty -> false

let st_set st (b, res) =
    st.solved <- b;
    st.todo <- st.todo @ res

(* Extension functions *)
let add_expr, remove_expr, to_do =
    let st = empty_state in
    let is_new e = not (List.exists (fun (e', _) -> equal e e') st.todo) in
    let add e = (* try and compute a solution *)
        if is_new e && not st.solved then begin
            try
                let f = of_bexpr e in
                let s = st_head st in
                let s' = simplex_add s f in
                st_push st (e, s');
                st_set st (simplex_solve s')
            with NotaFormula -> ()
        end
    and remove e = if st_is_head st e then st_pop st
    and to_do e = snd (List.find (fun (e', _) -> equal e e') st.todo)
    in
    add, remove, to_do

(* TODO: rewrite these *)
let lesseq a b = eapp ("$lesseq", [a; b])
let greatereq a b = eapp ("$greatereq", [a; b])
let minus_one e = eapp ("$difference", [e; eapp ("$int", [evar "1"])])
let plus_one e = eapp ("$sum", [e; eapp ("$int", [evar "1"])])

let newnodes e g _ =
    try
        [to_do e]
    with Not_found -> begin match e with
    | Enot (Eapp ("$eq_$int", [a; b], _), _) -> [Node {
        nconc = [e];
        nrule = Ext ("arith", "neq", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [lesseq a (minus_one b)]; [greatereq a (plus_one b)] |]; }]
    | _ -> []
    end

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
  Extension.add_formula = add_expr;
  Extension.remove_formula = remove_expr;
  Extension.preprocess = (fun x -> x);
  Extension.add_phrase = (fun _ -> ());
  Extension.postprocess = (fun x -> x);
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;

