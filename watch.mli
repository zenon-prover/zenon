(* Copyright 2004 INRIA. *)
(** watches some external symbols in order to know if they are really used in
  the generated coq proof or not.
*)

(** adds a new hypothesis to watch. *)
val watch_hyp: string -> unit

(** adds a new definition to watch. *)
val watch_def: string -> unit

(** specifies that the given hypothesis is used in the proof. *)
val use_hyp: string -> unit

(** specifies that the given definition is used in the proof. *)
val use_def: string -> unit

(** assumes silently that the definitions are indeed unfolded. *)
val force_definitions_use: unit -> unit

(** empties the tables. *)
val clear_watch: unit -> unit

(** if warning are enabled, outputs on stderr the list of unused symbols. 
  The given string is the name of the theorem.
*)
val warn_unused: string -> unit
