(*  Copyright 2005 INRIA  *)
Version.add "$Id: error.ml,v 1.2 2005-11-05 11:13:17 doligez Exp $";;

let warnings_flag = ref true;;
let err_file = ref "";;

let print_header = ref false;;
let header = ref "";;

let set_header msg =
  print_header := true;
  header := msg;
;;

let warn msg =
  let oc = if !err_file <> "" then open_out !err_file else stderr in
  if !warnings_flag then begin
    if !print_header then begin
      Printf.fprintf oc "%s\n" !header;
      print_header := false;
    end;
    Printf.fprintf oc "Warning: %s.\n" msg;
    flush stderr;
  end;
  if !err_file <> "" then close_out oc;
;;

exception Lex_error of string;;
