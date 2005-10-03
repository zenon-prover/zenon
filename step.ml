(*  Copyright 2004 INRIA  *)
Version.add "$Id: step.ml,v 1.4.2.1 2005-10-03 10:22:30 doligez Exp $";;

open Printf;;

type condition =
  | Count of int * bool
  | String of string
;;

let cond = ref (Count (0, false));;

let str_tail s =
  String.sub s 1 (String.length s - 1)
;;

let rec pause () =
  eprintf " >>> ";
  flush stderr;
  let l = read_line () in
  let len = String.length l in
  if len = 0 then Count (0, false)
  else begin
    match l.[0] with
    | '0' .. '9' -> Count (int_of_string l, false)
    | '/' -> String (str_tail l)
    | '.' when len = 1 -> Count (0, true)
    | '.' -> Count (int_of_string (str_tail l), true)
    | 'q' -> failwith "exit"
    | _ ->
       fprintf stderr "please type [.]<num> or /<string> or q\n";
       flush stderr;
       pause ()
  end
;;

let b = Buffer.create 1000;;

let ifstep action =
  if !Globals.debug_flag then begin
    match !cond with
    | Count (n, silent) when n > 0 ->
       if not silent then begin
         Buffer.reset b;
         action b;
         Buffer.output_buffer stderr b;
         eprintf "\n";
         flush stderr;
       end;
       cond := Count (n-1, silent);
    | Count (_, _) ->
       Buffer.reset b;
       action b;
       Buffer.output_buffer stderr b;
       cond := pause ();
    | String s ->
       Buffer.reset b;
       action b;
       let msg = Buffer.contents b in
       Buffer.output_buffer stderr b;
       if Misc.occurs s msg then cond := pause () else eprintf "\n";
       flush stderr;
  end;
;;

let forms msg fs =
  ifstep (fun b ->
    bprintf b "#### %s: " msg;
    let f init e =
      bprintf b "%s[%d]" init (Index.get_number e);
      Print.expr_soft (Print.Buff b) e;
    in
    match fs with
    | [] | [_] -> List.iter (f "") fs;
    | _ -> List.iter (f "\n    ") fs;
  )
;;

let rule msg r =
  ifstep (fun b ->
    bprintf b "#### %s: " msg;
    Print.mlproof_rule_soft (Print.Buff b) r;
    bprintf b " ";
  )
;;
