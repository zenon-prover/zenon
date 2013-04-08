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

(** {2 Curryfied terms} *)

module CurryfiedTerm = struct
  type t = {
    shape : shape;      (** Which kind of term is it? *)
    mutable tag : int;  (** Unique ID *)
  }
  and shape =
    | Const of int      (** Constant *)
    | Apply of t * t    (** Curryfied application *)

  type term = t

  module WE = Weak.Make(struct
    type t = term
    let equal a b = match a.shape, b.shape with
      | Const ia, Const ib -> ia = ib
      | Apply (a1,a2), Apply (b1,b2) -> a1 == a2 && b1 == b2
      | _ -> false
    let hash a = match a.shape with
      | Const i -> i
      | Apply (a, b) -> a.tag * 65539 + b.tag
  end)

  let __table = WE.create 10001
  let count = ref 0

  let hashcons t =
    let t' = WE.merge __table t in
    (if t == t' then incr count);
    t'

  let mk_const i =
    let t = {shape=Const i; tag= !count; } in
    hashcons t

  let mk_app a b =
    let t = {shape=Apply (a, b); tag= !count; } in
    hashcons t

  let get_id t = t.tag
end

(** {2 Persistent Union-Find} *)

module type S = sig
  type elt
    (** Elements of the Union-find *)

  type t
    (** An instance of the union-find, ie a set of equivalence classes *)

  val create : int -> t
    (** Create a union-find of the given size. *)

  val find : t -> elt -> t
    (** [find uf a] returns the current representative of [a] in the given
        union-find structure [uf]. By default, [find uf a = a]. *)

  val union : t -> elt -> elt -> t
    (** [union uf a b] returns an update of [uf] where [find a = find b]. *)

  val iter_equiv_class : t -> elt -> (elt -> unit) -> unit
    (** [iter_equiv_class uf a f] calls [f] on every element of [uf] that
        is congruent to [a], including [a] itself. *)
end

module Make(X : ID) : S with type elt = X.t = struct
  type elt = X.t

  type t = {
    mutable parent : int PArray.t;      (* idx of the parent, with path compression *)
    mutable elt : elt option PArray.t;  (* ID -> element *)
    next : int PArray.t;                (* linked list of representative class *)
  } (** An instance of the union-find, ie a set of equivalence classes *)

  (** Create a union-find of the given size. *)
  let create size =
    { parent = PArray.init size (fun i -> i);
      elt = PArray.make size None;
      next = PArray.init size (fun i -> i);
    }

  (* ensure the arrays are big enough for [id], and set [elt.(id) <- elt] *)
  let ensure uf id elt =
    if id >= PArray.length uf.elt then begin
      (* resize *)
      let len = id + (id / 2) in
      PArray.extend_init uf.parent len (fun i -> i);
      PArray.extend uf.elt len None;
      PArray.extend_init uf.next len (fun i -> i);
    end;
    match PArray.get uf.elt id with
    | None -> uf.elt <- PArray.set uf.elt id (Some elt)
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
    match PArray.get uf.elt id' with
    | Some elt' -> elt'
    | None -> assert false

  (** [union uf a b] returns an update of [uf] where [find a = find b]. *)
  let union uf a b =
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
        (* concatenation of circular linked lists (equivalence classes) *)
        let next_a = PArray.get uf.next ia' in
        let next_b = PArray.get uf.next ib' in
        let next = PArray.set uf.next ia' next_b in
        let next = PArray.set next ib' next_a in
        { uf with parent; next; }

  (** [iter_equiv_class uf a f] calls [f] on every element of [uf] that
      is congruent to [a], including [a] itself. *)
  let iter_equiv_class uf a f =
    let ia = X.get_id a in
    ensure uf ia a;
    let rec traverse id =
      match PArray.get uf.elt id with
      | None -> assert false
      | Some elt ->
        f elt;  (* yield element *)
        let id' = PArray.get uf.next id in
        if id' = ia
          then ()  (* traversed the whole list *)
          else traverse id'
    in
    traverse ia
end
