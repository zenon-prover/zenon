(*  Copyright 2009 INRIA  *)
(*  $Id: enum.mli,v 1.1 2009-09-11 13:24:21 doligez Exp $  *)

(* Expansion of repeating text with counters. *)

val expand_string : int -> string -> string;;
(** Expand a template. *)

val expand_string_rev : int -> string -> string;;
(** Expand a template in reverse order. *)

val expand_text : int -> string -> string;;
(** Read the text and expand all the templates found between ,,, and ...
    If an template starts and ends with a newline (LF or CRLF), and 
    it doesn't work as a plain template, remove the first and last
    newlines and try again. *)
