(*  Copyright 2004 INRIA  *)
Version.add "$Id: step.ml,v 1.4 2004-09-09 15:25:35 doligez Exp $";;

open Printf;;

let pause () =
  let l = read_line () in
  try let result = int_of_string l in if result >= 1 then result else 1
  with Failure _ -> 1
;;

let ifstep action =
  if !Globals.debug_count > 0 then begin
    decr Globals.debug_count;
    if !Globals.debug_count = 0 then begin
      action ();
      Globals.debug_count := pause ();
    end;
  end;
;;

let forms msg fs =
  ifstep (fun () ->
    printf "#### %s: " msg;
    List.iter (fun (e, g) -> Print.expr_soft e; printf ", ") fs;
  )
;;

let rule msg r =
  ifstep (fun () ->
    printf "#### %s: " msg;
    Print.mlproof_rule_soft r;
  )
;;
