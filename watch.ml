(* Copyright 2004 INRIA. *)
(* $Id: watch.ml,v 1.1 2004-11-09 10:22:17 prevosto Exp $ *)
(* ajout Virgile 2004-11-08: tables des symboles a surveiller pour voir s'ils 
   sont reellement utilises dans la preuve. *)
let hyps = Hashtbl.create 13
let defs = Hashtbl.create 13

let watch_hyp name = Hashtbl.add hyps name true
let watch_def name = Hashtbl.add defs name true

let use tbl name = 
  try
    if (Hashtbl.find tbl name) then Hashtbl.replace tbl name false
  with Not_found -> ()

let use_hyp name = use hyps name
let use_def name = use defs name

let assume_use_definition = ref false
let force_definitions_use () = assume_use_definition:=true

let clear_watch () = 
  Hashtbl.clear hyps;
  Hashtbl.clear defs


let warn_unused th_name =
  if !Globals.warnings_flag then
    begin
      let init = ref false in
      let print_warn prefix name unused = 
        if unused then
          begin
            if not !init then
              begin
                init:=true;
                Printf.eprintf "In theorem %s:\n" th_name
              end;
            Printf.eprintf 
              "Warning: %s %s is unused in the proof.\n" prefix name
          end
      in 
        Hashtbl.iter (print_warn "hypothesis") hyps;
        if not (!assume_use_definition) then
          Hashtbl.iter (print_warn "definition") defs;
        flush stderr
    end;

  

