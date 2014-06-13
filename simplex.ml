
(* TODO: Use Arrays instead of lists. *)
(* OPTIMS:
 * - distinguish separate systems (that do not interact), such as in { 1 <= 3x = 3y <= 2; z <= 3}.
 * - Implement gomorry cuts ?
*)

(* Signature for the variable type *)
module type OrderedType = sig
    type t
    val compare : t -> t -> int
end

(* Output signature for the simplex module *)
module type S = sig

    type var
    type t
    type 'cert res =
        | Solution of (var * Q.t) list
        | Unsatisfiable of 'cert
    type k_cert = var * (Q.t * var) list
    type n_cert = cert_tree option ref
    and cert_tree =
            | Branch of var * Z.t * n_cert * n_cert
            | Explanation of k_cert
    type k_res = k_cert res
    type n_res = n_cert res
    type optim =
        | Tight of var
        | Multiply of var *  Q.t
    type debug_printer = Format.formatter -> t -> unit

    (* Simplex construction *)
    val empty       : t
    val add_eq      : t -> var * (Q.t * var) list -> t
    val add_bounds  : t -> var * Q.t * Q.t -> t
    (* Simplex solving *)
    val ksolve      : ?debug:(Format.formatter -> t -> unit) -> t -> k_res
    val nsolve      : t -> (var -> bool) -> n_res
    val nsolve_safe : t -> (var -> bool) -> Q.t * n_res
    val nsolve_incr : t -> (var -> bool) -> (unit -> n_res option)
    (* Optimization functions *)
    val tighten      : (var -> bool) -> t -> optim list
    val normalize    : (var -> bool) -> t -> optim list
    val preprocess   : t -> (var -> bool) -> optim list
    val apply_optims : (t -> optim list) list -> t -> optim list
    (* Access functions *)
    val get_tab     : t -> var list * var list * Q.t list list
    val get_assign  : t -> (var * Q.t) list
    val get_full_assign : t -> (var * Q.t) list
    val get_bounds  : t -> var -> Q.t * Q.t
    val get_all_bounds : t -> (var * (Q.t * Q.t)) list
    (* Printing functions *)
    val print_debug : (Format.formatter -> var -> unit) -> (Format.formatter -> t -> unit)
end

(* Simplex Implementation *)
module Make(Var: OrderedType) = struct

    module M = Map.Make(Var)

    (* Exceptions *)
    exception Unsat of Var.t
    exception SolutionFound of (Var.t * Q.t) list
    exception AbsurdBounds of Var.t
    exception NoneSuitable
    exception UnExpected of string

    (* Type declarations *)
    type var = Var.t
    type t = {
        mutable tab : Q.t list list;
        mutable basic : Var.t list;
        mutable nbasic : Var.t list;
        mutable assign : Q.t M.t;
        mutable bounds : (Q.t * Q.t) M.t; (* (lower, upper) *)
    }

    type 'cert res =
        | Solution of (Var.t * Q.t) list
        | Unsatisfiable of 'cert

    type k_cert = var * (Q.t * var) list
    type n_cert = cert_tree option ref
    and cert_tree =
            | Branch of Var.t * Z.t * n_cert * n_cert
            | Explanation of k_cert

    type k_res = k_cert res
    type n_res = n_cert res

    type debug_printer = Format.formatter -> t -> unit

    (* Base manipulation functions *)
    let empty = {
        tab = [];
        basic = [];
        nbasic = [];
        assign = M.empty;
        bounds = M.empty;
    }

    let mem x l = List.exists (fun y -> Var.compare x y = 0) l

    let rec empty_expr n = if n = 0 then [] else Q.zero :: (empty_expr (n - 1))

    let find_expr_basic t x =
        let rec aux l l' = match l,l' with
        | a :: r, e :: r' ->
                if Var.compare x a = 0 then
                    e
                else
                    aux r r'
        | [], [] -> raise (UnExpected "Trying to find an expression for a non-basic variable.")
        | _ -> raise (UnExpected "Internal representation error : different list length")
        in
        aux t.basic t.tab

    let find_expr_nbasic t x = List.map (fun y -> if Var.compare x y = 0 then Q.one else Q.zero) t.nbasic

    let find_expr_total t x =
        if mem x t.basic then
            find_expr_basic t x
        else if mem x t.nbasic then
            find_expr_nbasic t x
        else
            raise (UnExpected "Unknown variable")

    let value t x =
        try
            M.find x t.assign
        with Not_found ->
            try
                let lval = List.map (fun v' -> M.find v' t.assign) t.nbasic in
                List.fold_left Q.add Q.zero (List.map2 Q.mul lval (find_expr_basic t x))
            with Not_found ->
                raise (UnExpected "Basic variable in expression of a basic variable.")

    let get_bounds t x = try M.find x t.bounds with Not_found -> Q.minus_inf, Q.inf

    let is_within t x =
        let v = value t x in
        let low, upp = get_bounds t x in
        if Q.compare v low <= -1 then
            (false, low)
        else if Q.compare v upp >= 1 then
            (false, upp)
        else
            (true, v)

    let add_var t x =
        if mem x t.basic || mem x t.nbasic then
            t
        else
            { t with
                tab = List.map (fun l -> Q.zero :: l) t.tab;
                nbasic = x :: t.nbasic;
                assign = M.add x Q.zero t.assign;
            }

    let add_vars t l = List.fold_left add_var t l

    let add_eq t (s, eq) =
        if mem s t.basic || mem s t.nbasic then
            raise (UnExpected "Variable already defined.");
        let t = add_vars t (List.map snd eq) in
        let l_eq = List.map (fun (c, x) -> List.map (fun y -> Q.mul c y) (find_expr_total t x)) eq in
        let t_eq = List.fold_left (List.map2 Q.add) (empty_expr (List.length t.nbasic)) l_eq in
        { t with
            tab = t_eq :: t.tab;
            basic = s :: t.basic;
        }

    let add_bound_aux t (x, low, upp) =
        let t = add_var t x in
        let l, u = get_bounds t x in
        { t with bounds = M.add x (Q.max l low, Q.min u upp) t.bounds }

    let add_bounds t (x, l, u) =
        let t = add_bound_aux t (x, l, u) in
        if mem x t.nbasic then
            let (b, v) = is_within t x in
            if b then
                t
            else
                { t with assign = M.add x v t.assign }
        else
            t

    (* Modifies bounds in place. Do NOT export. *)
    let add_bounds_imp ?force:(b=false) t (x, l, u) =
        if mem x t.basic || mem x t.nbasic then begin
            if b then
                t.bounds <- M.add x (l, u) t.bounds
            else
                let low, upp = get_bounds t x in
                t.bounds <- M.add x (Q.max l low, Q.min u upp) t.bounds;
            if mem x t.nbasic then
                let (b, v) = is_within t x in
                if not b then
                t.assign <- M.add x v t.assign
        end else
            raise (UnExpected "Variable doesn't exists")

    let change_bounds = add_bounds_imp ~force:true

    let get_full_assign t = List.map (fun x -> (x, value t x)) (List.sort Var.compare (t.nbasic @ t.basic))

    let find_suitable t x =
        let _, v = is_within t x in
        let b = Q.lt (value t x) v in
        let test y a =
            let v = value t y in
            let low, upp = get_bounds t y in
            if b then
                (Q.lt v upp && Q.gt a Q.zero) || (Q.gt v low && Q.lt a Q.zero)
            else
                (Q.gt v low && Q.gt a Q.zero) || (Q.lt v upp && Q.lt a Q.zero)
        in
        let rec aux l1 l2 = match l1, l2 with
            | [], [] -> []
            | y :: r1, a :: r2 ->
                    if test y a then
                        (y, a) :: (aux r1 r2)
                    else
                        aux r1 r2
            | _, _ -> raise (UnExpected "Wrong list size")
        in
        try
            List.hd (List.sort (fun x y -> Var.compare (fst x) (fst y)) (aux t.nbasic (find_expr_basic t x)))
        with Failure _ ->
            raise NoneSuitable

    let rec find_and_replace x l1 l2 =
        let res = ref Q.zero in
        let l = List.map2
        (fun a y -> if Var.compare x y = 0 then begin res := a; Q.zero end else a) l1 l2 in
        !res, l

    let pivot t x y a =
        let l = List.map2
            (fun b z -> if Var.compare y z = 0 then Q.inv a else Q.neg (Q.div b a))
            (find_expr_basic t x) t.nbasic in
        List.map2 (fun z e ->
            if Var.compare x z = 0 then l else
                let k, l' = find_and_replace y e t.nbasic in
                List.map2 Q.add l' (List.map (fun n -> Q.mul k n) l)) t.basic t.tab

    let subst x y l = List.map (fun z -> if Var.compare x z = 0 then y else z) l

    let rec solve_aux debug t =
        debug t;
        M.iter (fun x (l, u) -> if Q.gt l u then raise (AbsurdBounds x)) t.bounds;
        try
            while true do
                let x = List.find (fun y -> not (fst (is_within t y))) (List.sort Var.compare t.basic) in
                let _, v = is_within t x in
                try
                    let y, a = find_suitable t x in
                    t.tab <- pivot t x y a;
                    t.assign <- M.add x v (M.remove y t.assign);
                    t.basic <- subst x y t.basic;
                    t.nbasic <- subst y x t.nbasic;
                    debug t
                with NoneSuitable ->
                    raise (Unsat x)
            done;
        with Not_found -> ()

    let ksolve ?debug:(f=fun _ _ -> ()) t =
        let f = f Format.err_formatter in
        try
            solve_aux f t;
            Solution (get_full_assign t)
        with
        | Unsat x ->
                Unsatisfiable (x, List.combine (find_expr_basic t x) t.nbasic)
        | AbsurdBounds x ->
                Unsatisfiable (x, [])

    (* TODO: is there a better way to do this ? *)
    let is_z v = Z.equal (Q.den v) Z.one
    let is_q v = not (Z.equal (Q.den v) Z.zero || is_z v)

    let denlcm = List.fold_left (fun k c -> if Q.is_real c then Z.lcm k (Q.den c) else k) Z.one

    let lgcd k expr =
        let expr = List.filter (fun v -> Q.is_real v && not (Q.equal v Q.zero)) expr in
        let aux = (fun g c -> Z.gcd g (Q.to_bigint (Q.mul c k))) in
        Q.of_bigint (List.fold_left aux (Q.to_bigint (Q.mul (List.hd expr) k)) (List.tl expr))

    let global_bound t =
        let m, max_coef = M.fold (fun x (l, u) (m, max_coef) ->
            let m = m + (if Q.is_real l then 1 else 0) + (if Q.is_real u then 1 else 0) in
            let expr = find_expr_total t x in
            let k = Q.of_bigint (denlcm (l :: u :: expr)) in
            let k' = lgcd k expr in
            let max_coef = Z.max max_coef
                (Q.to_bigint (List.fold_left Q.max Q.zero (List.filter Q.is_real (List.map (fun x -> Q.abs (Q.div (Q.mul k x) k')) (l :: u :: expr))))) in
            m, max_coef
        ) t.bounds (0, Z.zero) in
        let n = max (List.length t.nbasic) m in
        Q.of_bigint (Z.pow (Z.mul (Z.of_int 2) (Z.mul (Z.pow (Z.of_int n) 2) max_coef)) n)

    let bound_all t int_vars g =
        List.fold_left (fun t x -> add_bounds t (x, Q.neg g, g)) t (List.filter int_vars t.nbasic)

    type optim =
        | Tight of Var.t
        | Multiply of Var.t * Q.t

    let floor v =
        try
            Q.of_bigint (Z.ediv (Q.num v) (Q.den v))
        with Division_by_zero -> v

    let ceil v = Q.neg (floor (Q.neg v))

    let normalize int_vars t =
        let mask = List.map int_vars t.nbasic in
        let aux x expr =
            let tmp = ref [] in
            let l, u = get_bounds t x in
            let k = Q.of_bigint (denlcm (l :: u :: expr)) in
            let k' = lgcd k expr in
            let k'' = Q.div k k' in
            if (List.for_all2 (fun b c -> b || Q.equal c Q.zero) mask expr) &&
                (not (Q.equal k' Q.one) && (not (is_z (Q.div (Q.mul l k) k')) || not (is_z (Q.div (Q.mul u k) k')))) then begin
                let low, upp = ceil (Q.mul l k''), floor (Q.mul u k'') in
                tmp := [Tight x];
                change_bounds t (x, low, upp)
            end else
                change_bounds t (x, Q.mul l k'', Q.mul u k'');
            (Multiply (x, k'') :: !tmp, List.map (fun c -> Q.mul c k'') expr)
        in
        let o, tab = List.fold_left2 (fun (opt_l, tab_l) x e ->
            let o, e' = aux x e in (o @ opt_l, e' :: tab_l)) ([], []) t.basic t.tab in
        t.tab <- tab;
        o

    let tighten int_vars t =
        let aux acc x =
            let l, u = get_bounds t x in
            if is_q l || is_q u then begin
                change_bounds t (x, ceil l, floor u);
                Tight x :: acc
            end else
                acc
        in
        List.fold_left aux [] (List.filter int_vars t.nbasic)

    let apply_optims l t =
        List.fold_left (fun acc f -> acc @ (f t)) [] l

    let preprocess t int_vars =
        let l = [
            tighten int_vars;
            normalize int_vars;
        ] in
        apply_optims l t

    (* Imperative implementation of the Branch&Bound *)

    (* Strangely here, using Queue instade of Stack leads to better perfomances *)
    (* TODO: insert user functions between iterations ? + debug function for ksolve ? *)
    let nsolve_aux max_depth t int_vars =
        let f = fun _ _ -> () in
        let to_do = Queue.create () in
        let final = ref None in
        Queue.push (0, t.bounds, (List.hd t.nbasic, Q.minus_inf, Q.inf), final) to_do;
        try
            while true do
                let depth, bounds, new_bound, res = Queue.pop to_do in
                if max_depth > 0 && depth > max_depth then
                    raise Exit;
                (* We can assume res = ref None *)
                try
                    t.bounds <- bounds;
                    add_bounds_imp t new_bound;
                    solve_aux f t;
                    let x = List.find (fun y -> not (is_z (value t y))) int_vars in
                    let v = value t x in
                    let v' = Z.ediv (Q.num v) (Q.den v) in
                    let under, above = (ref None), (ref None) in
                    res := Some (Branch (x, v', under, above));
                    Queue.push (depth + 1, t.bounds, (x, Q.of_bigint (Z.succ v'), Q.inf), above) to_do;
                    Queue.push (depth + 1, t.bounds, (x, Q.minus_inf, Q.of_bigint v'), under) to_do
                with
                | Not_found ->
                    raise (SolutionFound (get_full_assign t))
                | Unsat x ->
                        res := Some (Explanation (x, List.combine (find_expr_basic t x) t.nbasic))
                | AbsurdBounds x ->
                        res := Some (Explanation(x, []))
            done;
            raise (UnExpected "")
        with
        | Queue.Empty ->
                Unsatisfiable final
        | SolutionFound sol ->
                Solution sol

    let nsolve t int_vars =
        let init_bounds = t.bounds in
        if List.length t.nbasic = 0 then
            raise (Invalid_argument "Simplex is empty.");
        let res = nsolve_aux 0 t (List.filter int_vars (t.nbasic @ t.basic)) in
        t.bounds <- init_bounds;
        res

    let nsolve_safe t int_vars =
        let g = global_bound t in
        g, nsolve (bound_all t int_vars g) int_vars

    let base_depth t = 10 + 2 * (List.length t.nbasic)

    let nsolve_incr t int_vars =
        if List.length t.nbasic = 0 then
            raise (Invalid_argument "Simplex is empty.");
        let init_bounds = t.bounds in
        let int_vars = (List.filter int_vars (t.nbasic @ t.basic)) in
        let max_depth = ref (base_depth t) in
        let acc = ref None in
        let f () = match !acc with
            | Some _ -> !acc
            | None ->
                    try
                        let res = nsolve_aux !max_depth t int_vars in
                        t.bounds <- init_bounds;
                        acc := Some res;
                        Some (res)
                    with Exit ->
                        max_depth := 2 * !max_depth;
                        t.bounds <- init_bounds;
                        None
        in
        f

    let get_tab t = t.nbasic, t.basic, t.tab
    let get_assign t = M.bindings t.assign
    let get_all_bounds t = M.bindings t.bounds

    let print_bounds print_var fmt b =
        M.iter (fun x (l, u) -> Format.fprintf fmt "%s\t<= %a\t<= %s@\n" (Q.to_string l) print_var x (Q.to_string u)) b

    let print_tab print_var fmt (l, tab) =
        let aux fmt = List.iter (fun y -> Format.fprintf fmt "%s\t" (Q.to_string y)) in
        List.iter2 (fun x e -> Format.fprintf fmt "%a\t%a@\n" print_var x aux e) l tab

    let print_assign print_var fmt l =
        List.iter (fun (x, c) -> Format.fprintf fmt "%a -> %s;@ " print_var x (Q.to_string c)) l

    let print_debug print_var fmt t =
        Format.fprintf fmt "@[<hov 2>*** System state ***@\n\t%a@\n%aBounds:@\n%aCurrent assign:@\n%a@]@\n******** END ********@."
            (fun fmt -> List.iter (fun x -> Format.fprintf fmt "%a\t" print_var x)) t.nbasic
            (print_tab print_var) (t.basic, t.tab)
            (print_bounds print_var) t.bounds
            (print_assign print_var) (get_assign t)

end

module type HELPER = sig
  (** User provided variable type *)
  type external_var

  type var = private
    | Intern of int
    | Extern of external_var

  (** Fresh internal variable *)
  val fresh_var : unit -> var

  (** Lift an external variable in the [var] type *)
  val mk_var : external_var -> var

  (** the usual system, but the extended variable type *)
  include S with type var := var

  type monome = (Q.t * external_var) list

  type op = LessEq | Eq | GreaterEq

  type constraint_ = op * monome * Q.t

  val add_constraints : t -> constraint_ list -> t
end

module MakeHelp(Var : OrderedType) = struct
  type external_var = Var.t

  type var =
    | Intern of int
    | Extern of external_var

  let compare_var v1 v2 = match v1, v2 with
    | Intern i, Intern j -> Pervasives.compare i j
    | Intern _, Extern _ -> 1
    | Extern _, Intern _ -> -1
    | Extern v1, Extern v2 -> Var.compare v1 v2

  let fresh_var =
    let r = ref 0 in
    fun () ->
      let v = Intern !r in
      incr r;
      v

  let mk_var e = Extern e

  (* use the previous module *)
  module M = Make(struct
    type t = var
    let compare = compare_var
  end)
  include (M : S with type var := var)

  type monome = (Q.t * external_var) list

  type op = LessEq | Eq | GreaterEq

  type constraint_ = op * monome * Q.t

  (* normalize a monome *)
  let _normalize_monome l =
    (* merge together coefficients for the same variables *)
    let rec aux l = match l with
      | []
      | [_] -> l
      | (c,_)::l' when Q.equal c Q.zero -> aux l'
      | (c1,v1)::(c2,v2)::l' when compare_var v1 v2 = 0 ->
          aux ((Q.add c1 c2, v1)::l')
      | (c1,v1)::l' -> (c1,v1) :: aux l'
    in
    let l = List.map (fun (c,v) -> c, mk_var v) l in
    (* sort, then merge together *)
    let l = List.sort (fun (_,v1)(_,v2) -> compare_var v1 v2) l in
    aux l

  let add_constraints simpl l =
    List.fold_left
      (fun simpl c ->
        let op, m, const = c in
        let m = _normalize_monome m in
        (* obtain one coefficient and variable that have bounds *)
        let var, coeff, simpl =
          match m with
          | [c,v] -> v, c, simpl
          | _ ->
            let v = fresh_var () in
            let simpl = add_eq simpl (v, m) in
            v, Q.one, simpl
        in
        (* add bounds for the selected variable *)
        assert(Q.sign coeff <> 0);
        let const' = Q.div const coeff in
        match op with
        | Eq -> add_bounds simpl (var,const',const')
        | LessEq ->
            (* beware the multiplication by a negative number *)
            if Q.sign coeff < 0
              then add_bounds simpl (var,const',Q.inf)
              else add_bounds simpl (var,Q.minus_inf,const')
        | GreaterEq ->
            if Q.sign coeff < 0
              then add_bounds simpl (var,Q.minus_inf,const')
              else add_bounds simpl (var,const',Q.inf)
      ) simpl l
end
