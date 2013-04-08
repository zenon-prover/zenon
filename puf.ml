(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
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

(** {1 Functional (persistent) extensible union-find} *)

(** {2 Persistent array} *)

module PArray = struct
  type 'a t = 'a zipper ref
  and 'a zipper =
    | Array of 'a array
    | Diff of int * 'a * 'a t

  (* XXX maybe having a snapshot of the array from point to point may help? *)

  let make size elt =
    let a = Array.create size elt in
    ref (Array a)

  let init size f =
    let a = Array.init size f in
    ref (Array a)

  (** Recover the given version of the shared array. Returns the array
      itself. *)
  let rec reroot t =
    match !t with
    | Array a -> a
    | Diff (i, v, t') ->
      begin
        let a = reroot t' in
        let v' = a.(i) in
        t' := Diff (i, v', t);
        a.(i) <- v;
        t := Array a;
        a
      end

  let get t i =
    match !t with
    | Array a -> a.(i)
    | Diff _ -> 
      let a = reroot t in
      a.(i)

  let set t i v =
    let a =
      match !t with
      | Array a -> a
      | Diff _ -> reroot t in
    let v' = a.(i) in
    if v == v'
      then t (* no change *)
      else begin
        let t' = ref (Array a) in
        a.(i) <- v;
        t := Diff (i, v', t');
        t' (* create new array *)
      end

  let rec length t =
    match !t with
    | Array a -> Array.length a
    | Diff (_, _, t') -> length t'

  (** Extend [t] to the given [size], initializing new elements with [elt] *)
  let extend t size elt =
    let a = match !t with
    | Array a -> a
    | _ -> reroot t in
    if size > Array.length a
      then begin  (* resize: create bigger array *)
        let size = min Sys.max_array_length size in
        let a' = Array.make size elt in
        (* copy old part *)
        Array.blit a 0 a' 0 (Array.length a);
        t := Array a'
      end

  (** Extend [t] to the given [size], initializing elements with [f] *)
  let extend_init t size f =
    let a = match !t with
    | Array a -> a
    | _ -> reroot t in
    if size > Array.length a
      then begin  (* resize: create bigger array *)
        let size = min Sys.max_array_length size in
        let a' = Array.init size f in
        (* copy old part *)
        Array.blit a 0 a' 0 (Array.length a);
        t := Array a'
      end

  let fold_left f acc t =
    let a = reroot t in
    Array.fold_left f acc a
end

(** {2 Type with unique identifier} *)

module type ID = sig
  type t
  val get_id : t -> int
end

(** {2 Persistent Union-Find} *)

module type S = sig
  type elt
    (** Elements of the Union-find *)

  type t
    (** An instance of the union-find, ie a set of equivalence classes *)

  val create : int -> t
    (** Create a union-find of the given size. *)

  val find : t -> elt -> elt
    (** [find uf a] returns the current representative of [a] in the given
        union-find structure [uf]. By default, [find uf a = a]. *)

  val union : t -> elt -> elt -> t
    (** [union uf a b] returns an update of [uf] where [find a = find b].
        May raise Inconsistent. *)

  val distinct : t -> elt -> elt -> t
    (** Ensure that the two elements are distinct. May raise Inconsistent *)

  val must_be_distinct : t -> elt -> elt -> bool
    (** Should the two elements be distinct? *)

  val iter_equiv_class : t -> elt -> (elt -> unit) -> unit
    (** [iter_equiv_class uf a f] calls [f] on every element of [uf] that
        is congruent to [a], including [a] itself. *)

  val inconsistent : t -> (elt * elt) option
    (** Check whether the UF is inconsistent *)
end

module Make(X : ID) : S with type elt = X.t = struct
  type elt = X.t

  type t = {
    mutable parent : int PArray.t;      (* idx of the parent, with path compression *)
    mutable data : elt_data option PArray.t;   (* ID -> data for an element *)
    inconsistent : (elt * elt) option;  (* is the UF inconsistent? *)
  } (** An instance of the union-find, ie a set of equivalence classes *)
  and elt_data = {
    elt : elt;
    next : int;                         (* next element in equiv class *)
    distinct : int list;                (* classes distinct from this one *)
  }

  let get_data uf id =
    match PArray.get uf.data id with
    | Some data -> data
    | None -> assert false

  (** Create a union-find of the given size. *)
  let create size =
    { parent = PArray.init size (fun i -> i);
      data = PArray.make size None;
      inconsistent = None;
    }

  (* ensure the arrays are big enough for [id], and set [elt.(id) <- elt] *)
  let ensure uf id elt =
    if id >= PArray.length uf.data then begin
      (* resize *)
      let len = id + (id / 2) in
      PArray.extend_init uf.parent len (fun i -> i);
      PArray.extend uf.data len None;
    end;
    match PArray.get uf.data id with
    | None ->
      let data = { elt; next=id; distinct=[]; } in
      uf.data <- PArray.set uf.data id (Some data)
    | Some _ -> ()

  (* Find the ID of the root of the given ID *)
  let rec find_root uf id =
    let parent_id = PArray.get uf.parent id in
    if id = parent_id
      then id
      else begin (* recurse *)
        let root = find_root uf parent_id in
        (* path compression *)
        uf.parent <- PArray.set uf.parent id root;
        root
      end

  (** [find uf a] returns the current representative of [a] in the given
      union-find structure [uf]. By default, [find uf a = a]. *)
  let find uf elt =
    let id = X.get_id elt in
    (* get sure we can access arrays at index [id] *)
    ensure uf id elt;
    let id' = find_root uf id in
    match PArray.get uf.data id' with
    | Some data -> data.elt
    | None -> assert false

  (** [union uf a b] returns an update of [uf] where [find a = find b]. *)
  let union uf a b =
    (if uf.inconsistent <> None
      then raise (Invalid_argument "inconsistent uf"));
    let ia = X.get_id a in
    let ib = X.get_id b in
    ensure uf ia a;
    ensure uf ib b;
    (* indexes of roots of [a] and [b] *)
    let ia' = find_root uf ia
    and ib' = find_root uf ib in
    if ia' = ib'
      then uf  (* no change *)
      else
        (* merge roots (a -> b, arbitrarily) *)
        let parent = PArray.set uf.parent ia' ib' in
        (* data associated to both representatives *)
        let data_a = get_data uf ia' in
        let data_b = get_data uf ib' in
        (* merge 'distinct' lists: distinct(b) <- distinct(b)+distinct(a) *)
        let distinct' = List.rev_append data_a.distinct data_b.distinct in
        (* concatenation of circular linked lists (equivalence classes),
           concatenation of distinct lists *)
        let data_a' = {data_a with next=data_b.next; } in
        let data_b' = {data_b with next=data_a.next; distinct=distinct'; } in
        let data = PArray.set uf.data ia' (Some data_a') in
        let data = PArray.set data ib' (Some data_b') in
        (* inconsistency check *)
        let inconsistent =
          if List.exists (fun id -> find_root uf id = ib') data_a.distinct
            then Some (a, b)
            else None
        in
        { parent; data; inconsistent; }

  (** Ensure that the two elements are distinct. May raise Inconsistent *)
  let distinct uf a b =
    (if uf.inconsistent <> None
      then raise (Invalid_argument "inconsistent uf"));
    let ia = X.get_id a in
    let ib = X.get_id b in
    ensure uf ia a;
    ensure uf ib b;
    (* representatives of a and b *)
    let ia' = find_root uf ia in
    let ib' = find_root uf ib in
    (* check inconsistency *)
    let inconsistent = if ia' = ib' then Some (a, b) else None in
    (* update 'distinct' lists *)
    let data_a = get_data uf ia' in
    let data_a' = {data_a with distinct= ib' :: data_a.distinct; } in
    let data_b = get_data uf ib' in
    let data_b' = {data_b with distinct= ib' :: data_b.distinct; } in
    let data = PArray.set uf.data ia' (Some data_a) in
    let data = PArray.set data ib' (Some data_b) in
    { uf with inconsistent; data; }

  let must_be_distinct uf a b =
    let ia = X.get_id a in
    let ib = X.get_id b in
    ensure uf ia a;
    ensure uf ib b;
    (* representatives *)
    let ia' = find_root uf ia in
    let ib' = find_root uf ib in
    (* list of equiv classes that must be != a *)
    let distinct_a = (get_data uf ia').distinct in
    List.exists (fun id -> find_root uf id = ib') distinct_a

  (** [iter_equiv_class uf a f] calls [f] on every element of [uf] that
      is congruent to [a], including [a] itself. *)
  let iter_equiv_class uf a f =
    let ia = X.get_id a in
    ensure uf ia a;
    let rec traverse id =
      match PArray.get uf.data id with
      | None -> assert false
      | Some data ->
        f data.elt;  (* yield element *)
        let id' = data.next in
        if id' = ia
          then ()  (* traversed the whole list *)
          else traverse id'
    in
    traverse ia

  let inconsistent uf = uf.inconsistent
end
