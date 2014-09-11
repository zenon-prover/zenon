
(*
copyright (c) 2014, guillaume bury
all rights reserved.

redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* OPTIMS:
 * - distinguish separate systems (that do not interact), such as in { 1 <= 3x = 3y <= 2; z <= 3} ?
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
    val copy        : t -> t
    val add_eq      : t -> var * (Q.t * var) list -> t
    val add_bounds  : t -> ?strict_lower:bool -> ?strict_upper:bool -> var * Q.t * Q.t -> t
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
    (* Access functions, some are rewritten at the end of the module *)
    val get_tab         : t -> var list * var list * Q.t list list
    val get_assign      : t -> (var * Q.t) list
    val get_full_assign : t -> (var * Q.t) list
    val get_bounds      : t -> var -> Q.t * Q.t
    val get_all_bounds  : t -> (var * (Q.t * Q.t)) list
    (* Printing functions *)
    val print_debug : (Format.formatter -> var -> unit) -> debug_printer
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
    type erat = Q.t * Q.t

    type t = {
        tab : Q.t array array;
        basic : Var.t array;
        nbasic : Var.t array;
        mutable assign : erat M.t;
        mutable bounds : (erat * erat) M.t; (* (lower, upper) *)
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

    (* epsilon-rationals *)
    let ezero = Q.zero, Q.zero
    let mul k (a,e) = Q.((k * a, k * e))
    let sum (a,e1) (b,e2) = Q.((a + b, e1 + e2))
    let compare (a,e1) (b,e2) = match Q.compare a b with
        | 0 -> Q.compare e1 e2
        | x -> x

    let lt a b = compare a b < 0
    let gt a b = compare a b > 0

    let min x y = if compare x y <= 0 then x else y
    let max x y = if compare x y >= 0 then x else y

    let evaluate epsilon (a,e) = Q.(a + epsilon * e)

    (* Base manipulation functions *)
    let matrix_map f m =
        for i = 0 to Array.length m - 1 do
            for j = 0 to Array.length m.(0) - 1 do
                m.(i).(j) <- f i j m.(i).(j)
            done
        done

    let init_matrix line col f =
        let m = Array.make_matrix line col Q.zero in
        matrix_map (fun i j _ -> f i j) m;
        m

    let copy_array a = Array.init (Array.length a) (fun i -> a.(i))
    let copy_matrix m =
        if Array.length m = 0 then
            init_matrix 0 0 (fun i j -> Q.zero)
        else
            init_matrix (Array.length m) (Array.length m.(0)) (fun i j -> m.(i).(j))

    let empty = {
        tab = [| |];
        basic = [| |];
        nbasic = [| |];
        assign = M.empty;
        bounds = M.empty;
    }

    let copy t = {
        tab = copy_matrix t.tab;
        basic = copy_array t.basic;
        nbasic = copy_array t.nbasic;
        assign = t.assign;
        bounds = t.bounds;
    }

    let index x a =
        let i = ref (-1) in
        let j = ref 0 in
        while !i < 0 && !j < Array.length a do
            if Var.compare x a.(!j) = 0 then i := !j;
            incr j
        done;
        !i

    let mem x a = index x a >= 0

    let rec list_uniq = function
        | [] -> []
        | a :: r ->
                let l = list_uniq r in
                if List.exists (fun b -> Var.compare a b = 0) l then l else a :: l

    let rec empty_expr n = Array.make n Q.zero

    let find_expr_basic t x =
        match index x t.basic with
        | -1 -> raise (UnExpected "Trying to find an expression for a non-basic variable.")
        | i -> t.tab.(i)

    let find_expr_nbasic t x =
        Array.init (Array.length t.nbasic) (fun j -> if Var.compare x t.nbasic.(j) = 0 then Q.one else Q.zero)

    let find_expr_total t x =
        if mem x t.basic then
            find_expr_basic t x
        else if mem x t.nbasic then
            find_expr_nbasic t x
        else
            raise (UnExpected "Unknown variable")

    let find_coef t x y =
        match index x t.basic, index y t.nbasic with
        | -1, _ | _, -1 -> assert false
        | i, j -> t.tab.(i).(j)

    let value t x =
        try
            M.find x t.assign
        with Not_found ->
            try
                let res = ref ezero in
                let expr = find_expr_basic t x in
                for i = 0 to Array.length expr - 1 do
                    res := sum !res (mul expr.(i) (M.find t.nbasic.(i) t.assign))
                done;
                !res
            with Not_found ->
                raise (UnExpected "Basic variable in expression of a basic variable.")

    let get_bounds t x = try M.find x t.bounds with Not_found -> Q.((minus_inf, zero), (inf, zero))

    let is_within t x =
        let v = value t x in
        let low, upp = get_bounds t x in
        if compare v low <= -1 then
            (false, low)
        else if compare v upp >= 1 then
            (false, upp)
        else
            (true, v)

    let add_vars t l =
        let l = List.filter (fun x -> not (mem x t.basic || mem x t.nbasic)) l in
        let l = list_uniq l in
        if l = [] then
            t
        else begin
            let a = Array.of_list l in
            {
                tab = init_matrix (Array.length t.basic) (Array.length t.nbasic + Array.length a)
                    (fun i j -> if j < Array.length t.nbasic then t.tab.(i).(j) else Q.zero);
                basic = copy_array t.basic;
                nbasic = Array.append t.nbasic a;
                assign = List.fold_left (fun acc y -> M.add y ezero acc) t.assign l;
                bounds = t.bounds;
            }
        end

    let add_eq t (s, eq) =
        if mem s t.basic || mem s t.nbasic then
            raise (UnExpected "Variable already defined.");
        let t = add_vars t (List.map snd eq) in
        let new_eq = Array.make (Array.length t.nbasic) Q.zero in
        List.iter (fun (c, x) -> Array.iteri (fun i c' -> new_eq.(i) <- Q.(new_eq.(i) + c * c')) (find_expr_total t x)) eq;
        { t with
            tab = Array.append t.tab [| new_eq |];
            basic = Array.append t.basic [| s |];
        }

    let add_bound_aux t (x, low, upp) =
        let t = add_vars t [x] in
        let l, u = get_bounds t x in
        { t with bounds = M.add x (max l low, min u upp) t.bounds }

    let add_bounds t ?strict_lower:(slow=false) ?strict_upper:(supp=false) (x, l, u) =
        let t = copy t in
        let e1 = if slow then Q.one else Q.zero in
        let e2 = if supp then Q.neg Q.one else Q.zero in
        let t = add_bound_aux t (x, (l,e1), (u,e2)) in
        if mem x t.nbasic then
            let (b, v) = is_within t x in
            if b then
                t
            else
                { t with assign = M.add x v t.assign }
        else
            t

    (* Modifies bounds in place. Do NOT export. *)
    let add_bounds_imp ?force:(b=false) t ?strict_lower:(slow=false) ?strict_upper:(supp=false) (x, l, u) =
        let low = (l, if slow then Q.one else Q.zero) in
        let upp = (u, if supp then Q.neg Q.one else Q.zero) in
        if mem x t.basic || mem x t.nbasic then begin
            if b then
                t.bounds <- M.add x (low, upp) t.bounds
            else
                let low', upp' = get_bounds t x in
                t.bounds <- M.add x (max low low', min upp upp') t.bounds;
            if mem x t.nbasic then
                let (b, v) = is_within t x in
                if not b then
                t.assign <- M.add x v t.assign
        end else
            raise (UnExpected "Variable doesn't exists")

    let change_bounds = add_bounds_imp ~force:true

    let full_assign t = List.map (fun x -> (x, value t x))
        (List.sort Var.compare (Array.to_list t.nbasic @ Array.to_list t.basic))

    let solve_epsilon t =
        let emin = ref Q.minus_inf in
        let emax = ref Q.inf in
        M.iter (fun x ((low,e1), (upp,e2)) ->
            let v,e = value t x in
            if Q.(e - e1 > zero) then
                emin := Q.max !emin Q.((low - v) / (e - e1))
            else if Q.(e - e1 < zero) then (* shoudln't happen as *)
                emax := Q.min !emax Q.((low - v) / (e - e1));
            if Q.(e - e2 > zero) then
                emax := Q.min !emax Q.((upp - v) / (e - e2))
            else if Q.(e - e2 < zero) then
                emin := Q.max !emin Q.((upp - v) / (e - e2));
        ) t.bounds;
        if Q.equal Q.minus_inf !emin && Q.equal Q.inf !emax then
            Q.zero
        else if Q.gt !emin Q.zero then
            !emin
        else if Q.geq !emax Q.one then
            Q.one
        else
            !emax

    let get_full_assign t =
        let e = solve_epsilon t in
        let f = evaluate e in
        List.map (fun (x, v) -> (x, f v)) (full_assign t)

    let find_suitable t x =
        let _, v = is_within t x in
        let b = compare (value t x) v < 0 in
        let test y a =
            let v = value t y in
            let low, upp = get_bounds t y in
            if b then
                (lt v upp && Q.gt a Q.zero) || (gt v low && Q.lt a Q.zero)
            else
                (gt v low && Q.gt a Q.zero) || (lt v upp && Q.lt a Q.zero)
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
            List.hd (List.sort (fun x y -> Var.compare (fst x) (fst y))
                (aux (Array.to_list t.nbasic) (Array.to_list (find_expr_basic t x))))
        with Failure _ ->
            raise NoneSuitable

    let rec find_and_replace x l1 l2 =
        let res = ref Q.zero in
        let l = List.map2
        (fun a y -> if Var.compare x y = 0 then begin res := a; Q.zero end else a) l1 l2 in
        !res, l

    let subst x y a =
        let k = index x a in
        a.(k) <- y

    let pivot t x y a =
        (* Assignment change *)
        t.assign <- M.add x (value t x) (M.remove y t.assign);
        (* Matrix Pivot operation *)
        let kx = index x t.basic in
        let ky = index y t.nbasic in
        for j = 0 to Array.length t.nbasic - 1 do
            if Var.compare y t.nbasic.(j) = 0 then
                t.tab.(kx).(j) <- Q.inv a
            else
                t.tab.(kx).(j) <- Q.neg (Q.div t.tab.(kx).(j) a)
        done;
        for i = 0 to Array.length t.basic - 1 do
            if i <> kx then begin
                let c = t.tab.(i).(ky) in
                t.tab.(i).(ky) <- Q.zero;
                for j = 0 to Array.length t.nbasic - 1 do
                    t.tab.(i).(j) <- Q.(t.tab.(i).(j) + c * t.tab.(kx).(j))
                done
            end
        done;
        (* Switch x and y in basic and nbasiv vars *)
        subst x y t.basic;
        subst y x t.nbasic

    let rec solve_aux debug t =
        debug t;
        M.iter (fun x (l, u) -> if gt l u then raise (AbsurdBounds x)) t.bounds;
        try
            while true do
                let x = List.find (fun y -> not (fst (is_within t y))) (List.sort Var.compare (Array.to_list t.basic)) in
                let _, v = is_within t x in
                try
                    let y, a = find_suitable t x in
                    pivot t x y a;
                    t.assign <- M.add x v t.assign;
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
                Unsatisfiable (x, List.combine (Array.to_list (find_expr_basic t x)) (Array.to_list t.nbasic))
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
        let m, max_coef = M.fold (fun x ((l,_), (u,_)) (m, max_coef) ->
            let m = m + (if Q.is_real l then 1 else 0) + (if Q.is_real u then 1 else 0) in
            let expr = Array.to_list (find_expr_total t x) in
            let k = Q.of_bigint (denlcm (l :: u :: expr)) in
            let k' = lgcd k expr in
            let max_coef = Z.max max_coef
                (Q.to_bigint (List.fold_left Q.max Q.zero (List.filter Q.is_real (List.map (fun x -> Q.abs (Q.div (Q.mul k x) k')) (l :: u :: expr))))) in
            m, max_coef
        ) t.bounds (0, Z.zero) in
        let n = Pervasives.max (Array.length t.nbasic) m in
        Q.of_bigint (Z.pow (Z.mul (Z.of_int 2) (Z.mul (Z.pow (Z.of_int n) 2) max_coef)) n)

    let bound_all t int_vars g =
        List.fold_left (fun t x -> add_bounds t (x, Q.neg g, g)) t (List.filter int_vars (Array.to_list t.nbasic))

    type optim =
        | Tight of Var.t
        | Multiply of Var.t * Q.t

    let floor v =
        try
            Q.of_bigint (Z.ediv (Q.num v) (Q.den v))
        with Division_by_zero -> v

    let ceil v = Q.neg (floor (Q.neg v))

    let normalize int_vars t =
        let mask = List.map int_vars (Array.to_list t.nbasic) in
        let aux x expr =
            let tmp = ref [] in
            let (l,e1), (u,e2) = get_bounds t x in
            let s1 = not (Q.equal e1 Q.zero) in
            let s2 = not (Q.equal e2 Q.zero) in
            let k = Q.of_bigint (denlcm (l :: u :: expr)) in
            let k' = lgcd k expr in
            let k'' = Q.div k k' in
            if (List.for_all2 (fun b c -> b || Q.equal c Q.zero) mask expr) &&
                (not (Q.equal k' Q.one) && (not (is_z (Q.div (Q.mul l k) k')) || not (is_z (Q.div (Q.mul u k) k')))) then begin
                let low, upp = ceil (Q.mul l k''), floor (Q.mul u k'') in
                tmp := [Tight x];
                change_bounds t ~strict_lower:s1 ~strict_upper:s2 (x, low, upp)
            end else
                change_bounds t ~strict_lower:s1 ~strict_upper:s2 (x, Q.mul l k'', Q.mul u k'');
            (Multiply (x, k'') :: !tmp, List.map (fun c -> Q.mul c k'') expr)
        in
        let o, tab = List.fold_left2 (fun (opt_l, tab_l) x e ->
            let o, e' = aux x e in (o @ opt_l, e' :: tab_l)) ([], [])
            (Array.to_list t.basic) (List.map Array.to_list (Array.to_list t.tab)) in
        List.iteri (fun i l -> List.iteri (fun j k -> t.tab.(i).(j) <- k) l) tab;
        o

    let tighten int_vars t =
        let aux acc x =
            let (l,e1), (u,e2) = get_bounds t x in
            let s1 = not (Q.equal e1 Q.zero) in
            let s2 = not (Q.equal e2 Q.zero) in
            if is_q l || is_q u then begin
                change_bounds t ~strict_lower:s1 ~strict_upper:s2 (x, ceil l, floor u);
                Tight x :: acc
            end else
                acc
        in
        List.fold_left aux [] (List.filter int_vars (Array.to_list t.nbasic))

    let apply_optims l t =
        List.fold_left (fun acc f -> acc @ (f t)) [] l

    let preprocess t int_vars =
        let l = [
            tighten int_vars;
            normalize int_vars;
        ] in
        apply_optims l t

    (* Imperative implementation of the Branch&Bound *)

    (* TODO: insert user functions between iterations ? + debug function for ksolve ? *)
    let nsolve_aux max_depth t int_vars =
        let f = fun _ _ -> () in
        let to_do = Queue.create () in
        let final = ref None in
        Queue.push (0, t.bounds, (t.nbasic.(0), Q.minus_inf, Q.inf), final) to_do;
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
                    let x = List.find (fun y -> not (is_z (fst (value t y)))) int_vars in
                    let v, _ = value t x in
                    let v' = Z.ediv (Q.num v) (Q.den v) in
                    let under, above = (ref None), (ref None) in
                    res := Some (Branch (x, v', under, above));
                    Queue.push (depth + 1, t.bounds, (x, Q.of_bigint (Z.succ v'), Q.inf), above) to_do;
                    Queue.push (depth + 1, t.bounds, (x, Q.minus_inf, Q.of_bigint v'), under) to_do
                with
                | Not_found ->
                    raise (SolutionFound (get_full_assign t))
                | Unsat x ->
                        res := Some (Explanation (x, List.combine
                            (Array.to_list (find_expr_basic t x)) (Array.to_list t.nbasic)))
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
        if Array.length t.nbasic = 0 then
            raise (Invalid_argument "Simplex is empty.");
        let res = nsolve_aux 0 t (List.filter int_vars (Array.to_list t.nbasic @ Array.to_list t.basic)) in
        t.bounds <- init_bounds;
        res

    let nsolve_safe t int_vars =
        let g = global_bound t in
        g, nsolve (bound_all t int_vars g) int_vars

    let base_depth t = 100 + 2 * (Array.length t.nbasic)

    let nsolve_incr t int_vars =
        if Array.length t.nbasic = 0 then
            raise (Invalid_argument "Simplex is empty.");
        let init_bounds = t.bounds in
        let int_vars = (List.filter int_vars (Array.to_list t.nbasic @ Array.to_list t.basic)) in
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

    let get_tab t =
        Array.to_list t.nbasic,
        Array.to_list t.basic,
        List.map Array.to_list (Array.to_list t.tab)
    let get_assign t = List.map (fun (x, (v,e)) -> (x,v)) (M.bindings t.assign)
    let get_bounds t x = let ((l,_), (u,_)) = get_bounds t x in (l,u)
    let get_all_bounds t = List.map (fun (x,((l,_),(u,_))) -> (x, (l, u))) (M.bindings t.bounds)

    let pp_to_str f format =
        f Format.str_formatter format;
        Format.flush_str_formatter ()

    let tab_box var_to_string t =
        let a = Array.init (Array.length t.basic + 1) (fun i ->
                Array.init (Array.length t.nbasic + 1) (fun j ->
                    if i = 0 then
                        if j = 0 then
                            "..."
                        else
                            var_to_string (t.nbasic.(j - 1))
                    else
                        if j = 0 then
                            var_to_string (t.basic.(i - 1))
                        else (* i > 0 && j > 0 *)
                            Q.to_string t.tab.(i - 1).(j - 1)
                )) in
        PrintBox.grid_text ~pad:(PrintBox.hpad 1) ~bars:true a

    let bounds_box var_to_string t =
        let a = Array.make_matrix (M.cardinal t.bounds) 5 "<=" in
        let i = ref 0 in
        M.iter (fun x ((l,e1), (u,e2)) ->
            a.(!i).(0) <- Q.to_string l;
            if not (Q.equal e1 Q.zero) then a.(!i).(1) <- "<";
            a.(!i).(2) <- var_to_string x;
            if not (Q.equal e2 Q.zero) then a.(!i).(3) <- "<";
            a.(!i).(4) <- Q.to_string u;
            incr i;
        ) t.bounds;
        PrintBox.grid_text ~pad:(PrintBox.hpad 1) ~bars:false a

    let print_assign print_var fmt l =
        List.iter (fun (x, (c,e)) -> Format.fprintf fmt "%a -> %s + %s e;@ " print_var x (Q.to_string c) (Q.to_string e)) l

    let print_debug print_var fmt t =
        Format.fprintf fmt
            "@[*** System state ***@.%s@.%s@\n@[<hov 2>Current assign:@\n%a@]@\n******** END ********@."
            (PrintBox.to_string (tab_box (pp_to_str print_var) t))
            (PrintBox.to_string (bounds_box (pp_to_str print_var) t))
            (print_assign print_var) (M.bindings t.assign)

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

  type op = Less | LessEq | Eq | Greater | GreaterEq

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

  type op = Less | LessEq | Eq | Greater | GreaterEq

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
        | Less ->
            (* beware the multiplication by a negative number *)
            if Q.sign coeff < 0
              then add_bounds simpl ~strict_lower:true (var,const',Q.inf)
              else add_bounds simpl ~strict_upper:true (var,Q.minus_inf,const')
        | LessEq ->
            (* beware the multiplication by a negative number *)
            if Q.sign coeff < 0
              then add_bounds simpl (var,const',Q.inf)
              else add_bounds simpl (var,Q.minus_inf,const')
        | Greater ->
            if Q.sign coeff < 0
              then add_bounds simpl ~strict_upper:true (var,Q.minus_inf,const')
              else add_bounds simpl ~strict_lower:true (var,const',Q.inf)
        | GreaterEq ->
            if Q.sign coeff < 0
              then add_bounds simpl (var,Q.minus_inf,const')
              else add_bounds simpl (var,const',Q.inf)
      ) simpl l

end
