(*  Copyright 1997 INRIA  *)
Version.add "$Id: globals.ml,v 1.13 2004-10-18 16:53:28 doligez Exp $";;

open Printf;;

let debug_count = ref 0;;

let warnings_flag = ref true;;
let stats_flag = ref false;;
let quiet_flag = ref false;;
let size_limit = ref 100_000_000.;;
let time_limit = ref 300.;;
let short_flag = ref false;;
let ctx_flag = ref false;;

type progress = Progress_none | Progress_bar | Progress_messages;;
let progress_level = ref Progress_bar;;

let progress_cur = ref (-1);;
let progress_char = ref 0;;
let progress_anim = "/-\\|";;
let progress_bar = '*';;

let do_progress f =
  match !progress_level with
  | Progress_none -> ()
  | Progress_bar ->
      let tm = Sys.time () in
      let cur = int_of_float (60. *. tm /. !time_limit) in
      if !progress_cur = -1 then begin
        eprintf "%s" (String.make 61 ' ');
        eprintf "%s" (String.make 60 '\008');
        progress_cur := 0;
      end;
      if cur <> !progress_cur then begin
        eprintf "\008";
        for i = !progress_cur to cur - 1 do
          eprintf "%c" progress_bar;
        done;
        eprintf "%c" (progress_anim.[!progress_char]);
        progress_cur := cur;
      end else begin
        let c = (!progress_char + 1) mod (String.length progress_anim) in
        eprintf "\008%c" (progress_anim.[c]);
        progress_char := c;
      end;
      flush stderr;
  | Progress_messages ->
      flush stdout;
      flush stderr;
      f ();
      flush stdout;
      flush stderr;
;;

let end_progress msg =
  match !progress_level with
  | Progress_none -> ()
  | Progress_bar ->
     Printf.eprintf "\r";
     flush stderr;
  | Progress_messages ->
     if msg <> "" then Printf.eprintf "%s\n" msg;
     flush stderr;
;;

let inferences = ref 0;;
let proof_nodes = ref 0;;
let top_num_forms = ref 0;;
let stored_lemmas = ref 0;;
let num_expr = ref 0;;

let goal_found = ref false;;
