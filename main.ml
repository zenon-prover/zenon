(*  Copyright 1997 INRIA  *)
Misc.version "$Id: main.ml,v 1.4 2004-04-28 16:30:09 doligez Exp $";;

open Printf;;
open Globals;;

let formulas = ref [];;
let add_formula s = formulas := s :: !formulas;;

type proof_level = No_proof | Hl_proof of int | Ml_proof | Ll_proof;;
let proof_level = ref No_proof;;

let int_arg r arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    r := m *. (float_of_string arg1)
  in
  if l = 0 then raise (Arg.Bad "bad numeric argument")
  else
    try
      match arg.[l-1] with
      | 'k' -> multiplier 1_000.
      | 'M' -> multiplier 1_000_000.
      | 'G' -> multiplier 1_000_000_000.
      | 's' -> multiplier 1.
      | 'm' -> multiplier 60.
      | 'h' -> multiplier 3600.
      | 'd' -> multiplier 86400.
      | '0'..'9' -> r := float_of_string arg
      | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure "float_of_string" -> raise (Arg.Bad "bad numeric argument")
;;

let versions () =
  printf "zenon version 0.1.2 (2004-04-28)\n";
  Misc.print_versions ();
  exit 0;
;;

let argspec = [
  "-d", Arg.Unit (fun () -> Globals.step_count := 1),
      "        debug mode";
  "-h", Arg.String add_formula,
      "<form>  add formula <form> as hypothesis";
  "-hl", Arg.Int (fun n -> proof_level := Hl_proof n),
       "<n>    output proof in ML format up to depth <n>";
  "-ll", Arg.Unit (fun () -> proof_level := Ll_proof),
       "       output proof in LL format";
  "-max-size", Arg.String (int_arg size_limit),
             "<s>[kMG]  limit heap size to <s> kilo/mega/giga words"
             ^ " (default 100M)";
  "-max-time", Arg.String (int_arg time_limit),
             "<t>[smhd] limit CPU time to <t> second/minute/hour/day"
             ^ " (default 5m)";
  "-ml", Arg.Unit (fun () -> proof_level := Ml_proof),
       "       output proof in ML format";
  "-p", Arg.Unit (fun () -> progress_level := Progress_messages),
      "        turn on progress messages";
  "-q", Arg.Unit (fun () -> progress_level := Progress_none),
      "        turn off progress bar";
  "-s", Arg.Set stats_flag,
      "        print statistics";
  "-versions", Arg.Unit versions,
             " print version numbers and exit";
  "-w", Arg.Clear warnings_flag,
      "        suppress warnings";
  "-x", Arg.String Extension.activate,
      " <ext>  activate the extension <ext>"
];;

let files = ref [];;
let add_file s = files := s :: !files;;

let umsg = "Usage: zenon [options]";;

Arg.parse argspec add_file umsg;;


let parse_string s =
  let lexbuf = Lexing.from_string s in
  Parser.theory Lexer.token lexbuf
;;
let parse_string_list l = List.flatten (List.map parse_string l);;

let parse_file f =
  try
    let chan = open_in f in
    let lexbuf = Lexing.from_channel chan in
    if Filename.check_suffix f ".p" then begin
      let tpphrases = Parser.tpfile Lexer.tptoken lexbuf in
      close_in chan;
      Tptp.translate (Filename.dirname f) tpphrases
    end else if Filename.check_suffix f ".coz" then begin
      let result = Parser.coqfile Lexer.coqtoken lexbuf in
      close_in chan;
      result
    end else begin
      Globals.goal_found := false;
      let result = Parser.theory Lexer.token lexbuf in
      close_in chan;
      if (not !Globals.goal_found) && !Globals.warnings_flag then begin
        eprintf "Warning: no goal given.\n";
        flush stderr;
      end;
      result
    end
  with
  | Sys_error (msg) -> eprintf "%s\n" msg; exit 2
;;

Gc.set {(Gc.get ()) with
        Gc.minor_heap_size = 1_000_000;
        Gc.major_heap_increment = 1_000_000;
       }
;;

let main () =
  let phrases =
    if !formulas = [] && !files = [] then
      let lexbuf = Lexing.from_channel stdin in
      Parser.theory Lexer.token lexbuf
    else
      List.flatten (parse_string_list !formulas :: List.map parse_file !files)
  in
  let retcode = ref 0 in
  begin try
    let (defs, hyps) = Phrase.separate phrases in
    if !step_count > 0 then begin
      let ph_defs = List.map (fun x -> Phrase.Def x) defs in
      let ph_hyps = List.map (fun (x, y) -> Phrase.Hyp (x, y)) hyps in
      printf "initial formulas:\n";
      List.iter Print.phrase (ph_defs @ ph_hyps);
      printf "----\n";
      flush stdout;
      Gc.set {(Gc.get ()) with Gc.verbose = 0x010};
    end;
    let proof = Prove.prove defs hyps in
    printf "*** PROOF-FOUND ***\n"; flush stdout;
    match !proof_level with
    | No_proof -> eprintf "total proof size: %d nodes\n" (Mlproof.size proof);
    | Hl_proof n -> Print.hlproof n proof;
    | Ml_proof -> Print.mlproof proof;
    | Ll_proof -> Print.llproof (Mltoll.translate proof);
  with Prove.NoProof ->
    retcode := 10;
    printf "*** NO-PROOF ***\n"; flush stdout;
  end;
  if !stats_flag then begin
    eprintf "nodes searched: %d\n" !Globals.inferences;
    eprintf "max branch formulas: %d\n" !Globals.top_num_forms;
    eprintf "proof nodes created: %d\n" !Globals.proof_nodes;
    eprintf "formulas created: %d\n" !Globals.num_expr;
    eprintf "\n";
    Gc.print_stat stderr;
  end;
  exit !retcode;
;;

try main () with x -> flush stdout; raise x;;
