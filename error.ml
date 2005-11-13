(*  Copyright 2005 INRIA  *)
Version.add "$Id: error.ml,v 1.4 2005-11-13 22:49:11 doligez Exp $";;

open Printf;;

let warnings_flag = ref true;;
let err_file = ref "";;

let print_header = ref false;;
let header = ref "";;

let set_header msg =
  print_header := true;
  header := msg;
;;

let err_oc = ref stderr;;
let err_inited = ref false;;

let print kind msg =
  if not !err_inited then begin
    if !err_file <> "" then err_oc := open_out !err_file;
    if !print_header then fprintf !err_oc "%s\n" !header;
    err_inited := true;
  end;
  fprintf !err_oc "%s: %s\n" kind msg;
  flush !err_oc;
;;

let warn msg = if !warnings_flag then print "Warning" msg;;

let err msg = print "Error" msg;;

let errpos pos msg =
  let s = sprintf "File \"%s\", line %d, character %d:"
                  pos.Lexing.pos_fname pos.Lexing.pos_lnum
                  (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
  in
  print "" s;
  print "Error" msg;
;;

exception Lex_error of string;;
exception Abort;;
