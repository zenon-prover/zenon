(*  Copyright 1997 INRIA  *)
Version.add "$Id: main.ml,v 1.26 2005-11-13 22:49:11 doligez Exp $";;

open Printf;;
open Globals;;

type proof_level =
  | Proof_none
  | Proof_h of int
  | Proof_m
  | Proof_l
  | Proof_lx
  | Proof_coq
  | Proof_coqterm
;;
let proof_level = ref Proof_none;;

type input_format =
  | I_zenon
  | I_focal
  | I_tptp
;;
let input_format = ref I_zenon;;

let include_path = ref [];;

let opt_level = ref 1;;

(* Output file, script checking and validation *)
let outf = ref None

let set_out () =
  match !outf with
  | Some f -> open_out f
  | _ -> stdout
;;

let close_out oc =
  match !outf with
  | Some _ -> close_out oc
  | _ -> ()
;;

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
      | 'k' -> multiplier 1e3
      | 'M' -> multiplier 1e6
      | 'G' -> multiplier 1e9
      | 'T' -> multiplier 1e12
      | 's' -> multiplier 1.
      | 'm' -> multiplier 60.
      | 'h' -> multiplier 3600.
      | 'd' -> multiplier 86400.
      | '0'..'9' -> r := float_of_string arg
      | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure "float_of_string" -> raise (Arg.Bad "bad numeric argument")
;;

let parse_size_time s =
  let l = String.length s in
  let rec loop i =
    if i >= l then raise (Arg.Bad "bad size/time specification");
    if s.[i] = '/' then begin
      int_arg size_limit (String.sub s 0 i);
      int_arg time_limit (String.sub s (i+1) (l-i-1));
    end else begin
      loop (i+1);
    end;
  in
  loop 0;
;;

let short_version () =
  printf "zenon version %s\n" Version.full;
  exit 0;
;;

let cvs_version () =
  printf "zenon version %s\n" Version.full;
  Version.print_cvs stdout;
  exit 0;
;;

let files = ref [];;
let add_file s = files := s :: !files;;

let umsg = "Usage: zenon [options] <file>";;

let rec argspec = [
  "-", Arg.Unit (fun () -> add_file "-"),
    "                  read input from stdin";
  "-context", Arg.Set ctx_flag,
           "           provide context for checking the proof independently";
  "-d", Arg.Unit (fun () -> Globals.debug_flag := true;
                            Progress.level := Progress.No),
     "                 debug mode";
  "-errmsg", Arg.String Error.set_header,
          "<message>   prefix warnings and errors with <message>";
  "-help", Arg.Unit print_usage,
        "              print this option list and exit";
  "--help", Arg.Unit print_usage,
         "             print this option list and exit";
  "-I", Arg.String (fun x -> include_path := x :: !include_path),
     " <dir>           add <dir> to the include path (for TPTP input format)";
  "-iz", Arg.Unit (fun () -> input_format := I_zenon),
      "                read input file in zenon format (default)";
  "-ifocal", Arg.Unit (fun () -> input_format := I_focal),
          "            read input file in focal format";
  "-itptp", Arg.Unit (fun () -> input_format := I_tptp),
         "             read input file in TPTP format";
  "-max", Arg.String parse_size_time,
       "<s>[kMGT]/<t>[smhd]   Set both size and time limit (see below)";
  "-max-size", Arg.String (int_arg size_limit),
            "<s>[kMGT] limit heap size to <s> kilo/mega/giga/tera word"
            ^ " (default 100M)";
  "-max-time", Arg.String (int_arg time_limit),
            "<t>[smhd] limit CPU time to <t> second/minute/hour/day"
            ^ " (default 5m)";
  "-ocoq", Arg.Unit (fun () -> proof_level := Proof_coq),
        "              print the proof in Coq script format";
  "-ocoqterm", Arg.Unit (fun () -> proof_level := Proof_coqterm),
            "          print the proof in Coq term format";
  "-oh", Arg.Int (fun n -> proof_level := Proof_h n),
      "<n>             print the proof in high-level format up to depth <n>";
  "-ol", Arg.Unit (fun () -> proof_level := Proof_l),
      "                print the proof in low-level format";
  "-olx", Arg.Unit (fun () -> proof_level := Proof_lx),
       "               print the proof in raw low-level format";
  "-om", Arg.Unit (fun () -> proof_level := Proof_m),
      "                print the proof in middle-level format";
  "-onone", Arg.Unit (fun () -> proof_level := Proof_none),
         "             do not print the proof (default)";
  "-opt0", Arg.Unit (fun () -> opt_level := 0),
        "              do not optimise the proof";
  "-opt1", Arg.Unit (fun () -> opt_level := 1),
        "              do peephole optimisation of the proof (default)";
  "-p0", Arg.Unit (fun () -> Progress.level := Progress.No),
      "                turn off progress bar and progress messages";
  "-p1", Arg.Unit (fun () -> Progress.level := Progress.Bar),
      "                display progress bar (default)";
  "-p2", Arg.Unit (fun () -> Progress.level := Progress.Msg),
      "                display progress messages";
  "-q", Arg.Set quiet_flag,
     "                 suppress proof-found/no-proof/begin-proof/end-proof";
  "-stats", Arg.Set stats_flag,
         "             print statistics";
  "-short", Arg.Set short_flag,
         "             output a less detailed proof";
  "-v", Arg.Unit short_version,
     "                 print version string and exit";
  "-versions", Arg.Unit cvs_version,
            "          print CVS version strings and exit";
  "-w", Arg.Clear Error.warnings_flag,
     "                 suppress warnings";
  "-wout", Arg.Set_string Error.err_file,
        "<file>        output errors and warnings to <file> instead of stderr";
  "-x", Arg.String Extension.activate,
     "<ext>            activate extension <ext>"
]

and print_usage () =
  Arg.usage argspec umsg;
  exit 0;
;;

try Arg.parse argspec add_file umsg
with Not_found -> exit 2
;;

let report_error lexbuf msg =
  let p = Lexing.lexeme_start_p lexbuf in
  Error.errpos p msg;
  exit 2;
;;

let parse_file f =
  try
    let (name, chan, close) =
      if f = "-" then ("", stdin, ignore) else (f, open_in f, close_in)
    in
    let lexbuf = Lexing.from_channel chan in
    lexbuf.Lexing.lex_curr_p <- {
       Lexing.pos_fname = name;
       Lexing.pos_lnum = 1;
       Lexing.pos_bol = 0;
       Lexing.pos_cnum = 0;
    };
    try
      match !input_format with
      | I_tptp ->
          let tpphrases = Parsetptp.file Lextptp.token lexbuf in
          close chan;
          let d = Filename.dirname f in
          let pp = Filename.parent_dir_name in
          let upup = Filename.concat (Filename.concat d pp) pp in
          let incpath = List.rev (upup :: d :: !include_path) in
          let forms = Tptp.translate incpath tpphrases in
          let annotated = Tptp.process_annotations forms in
          let f x = (x, false) in
          (Tptp.get_thm_name (), List.map f annotated)
      | I_focal ->
          let (name, result) = Parsecoq.file Lexcoq.token lexbuf in
          close chan;
          (name, result)
      | I_zenon ->
          let phrases = Parsezen.file Lexzen.token lexbuf in
          close chan;
          let result = List.map (fun x -> (x, false)) phrases in
          let is_goal = function
            | (Phrase.Hyp ("z'goal", _, _), _) -> true
            | _ -> false
          in
          let goal_found = List.exists is_goal result in
          if not goal_found then Error.warn "no goal given";
          ("theorem", result)
    with
    | Parsing.Parse_error -> report_error lexbuf "syntax error."
    | Error.Lex_error msg -> report_error lexbuf msg
  with Sys_error (msg) -> Error.err msg; exit 2
;;

Gc.set {(Gc.get ()) with
        Gc.minor_heap_size = 1_000_000;
        Gc.major_heap_increment = 1_000_000;
       }
;;

let rec extract_strong accu phr_dep =
  match phr_dep with
  | [] -> accu
  | (p, true) :: t -> extract_strong (p::accu) t
  | (_, false) :: t -> extract_strong accu t
;;

let optim p =
  match !opt_level with
  | 0 -> p
  | 1 -> Llproof.optimise p
  | _ -> assert false
;;

let main () =
  let file = match !files with
             | [f] -> f
             | _ -> Arg.usage argspec umsg; exit 2
  in
  let (th_name, phrases_dep) = parse_file file in
  begin match !proof_level with
  | Proof_coq | Proof_coqterm -> Watch.warn_unused_var phrases_dep;
  | _ -> ()
  end;
  let retcode = ref 0 in
  begin try
    let strong_dep = extract_strong [] phrases_dep in
    let phrases = List.map fst phrases_dep in
    let ppphrases = Extension.preprocess phrases in
    let (defs, hyps) = Phrase.separate ppphrases in
    List.iter (fun (fm, _) -> Eqrel.analyse fm) hyps;
    let hyps = List.filter (fun (fm, _) -> not (Eqrel.subsumed fm)) hyps in
    if !debug_flag then begin
      let ph_defs = List.map (fun x -> Phrase.Def x) defs in
      let ph_hyps = List.map (fun (x, y) -> Phrase.Hyp ("", x, y)) hyps in
      eprintf "initial formulas:\n";
      List.iter (Print.phrase (Print.Chan stderr)) (ph_defs @ ph_hyps);
      eprintf "relations: ";
      Eqrel.print_rels stderr;
      eprintf "\n";
      eprintf "----\n";
      flush stderr;
      Gc.set {(Gc.get ()) with Gc.verbose = 0x010};
    end;
    let proof = Prove.prove defs hyps in
    if not !quiet_flag then begin
      printf "(* PROOF-FOUND *)\n";
      flush stdout;
    end;
    let llp = lazy (optim (Extension.postprocess
                             (Mltoll.translate th_name ppphrases proof)))
    in
    Watch.warn strong_dep llp;
    begin match !proof_level with
    | Proof_none -> ()
    | Proof_h n -> Print.hlproof (Print.Chan stdout) n proof;
    | Proof_m -> Print.mlproof (Print.Chan stdout) proof;
    | Proof_lx ->
        let lxp = Mltoll.translate th_name ppphrases proof in
        Print.llproof (Print.Chan stdout) lxp;
    | Proof_l -> Print.llproof (Print.Chan stdout) (Lazy.force llp);
    | Proof_coq -> Lltocoq.produce_proof stdout phrases (Lazy.force llp);
    | Proof_coqterm ->
        let p = Coqterm.trproof phrases (Lazy.force llp) in
        Coqterm.print stdout p;
    end;
  with Prove.NoProof ->
    retcode := 10;
    if not !quiet_flag then printf "(* NO-PROOF *)\n";
  end;
  if !stats_flag then begin
    eprintf "nodes searched: %d\n" !Globals.inferences;
    eprintf "max branch formulas: %d\n" !Globals.top_num_forms;
    eprintf "proof nodes created: %d\n" !Globals.proof_nodes;
    eprintf "formulas created: %d\n" !Globals.num_expr;
    eprintf "\n";
    (*Gc.print_stat stderr;*)
  end;
  exit !retcode;
;;

try main ()
with Error.Abort -> exit 11
;;
