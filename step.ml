(*  Copyright 2004 INRIA  *)
Version.add "$Id: step.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

open Printf;;

let pause () =
  let l = read_line () in
  try let result = int_of_string l in if result >= 1 then result else 1
  with Failure _ -> 1
;;

let ifstep action =
  if !Globals.step_count > 0 then begin
    decr Globals.step_count;
    if !Globals.step_count = 0 then begin
      action ();
      Globals.step_count := pause ();
    end;
  end;
;;

let forms msg fs =
  ifstep (fun () ->
    printf "%s: " msg;
    List.iter (fun (e, p) -> Print.expr_soft e; printf ", ") fs;
  )
;;

let rule msg r =
  ifstep (fun () ->
    printf "%s: " msg;
    Print.mlproof_rule_soft r;
  )
;;
