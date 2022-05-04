open Compile
open Runner
open Printf
open Lexing
open Exprs
open Errors
open Phases

let show_trace = ref false
let no_builtins = ref false
let filename_set = ref false
let alloc_strat = ref Naive
let filename : string ref = ref ""

let set_strategy s =
  match s with
  | "naive" -> alloc_strat := Naive
  | "register" -> alloc_strat := Register
  | _ -> raise (Arg.Bad (sprintf "'%s' is not an allocation strategy, use either naive or register" s))
;;
       
let () =
  let speclist = [
      ("-t", Arg.Set show_trace, "Display the trace of compilation");
      ("-no-builtins", Arg.Set no_builtins, "Leave out all built-in functions");
      ("-d", Arg.Set show_debug_print, "Enable debug printing");
      ("-alloc", Arg.String set_strategy, "Use register stack allocation")
    ] in
  Arg.parse speclist (fun name ->
      if !filename_set then
        raise (Arg.Bad "Cannot compile more than one file name")
      else
        (filename_set := true;
         filename := name)
    ) "Compiler options:";
  let sep = "\n=================\n" in
  match compile_file_to_string ~no_builtins:!no_builtins (!alloc_strat) (!filename) (!filename) with
  | Error (errs, trace) ->
     (if !show_trace then
        eprintf "%s%s" (ExtString.String.join sep (print_trace trace)) sep
      else ());
     eprintf "Errors:\n";
     eprintf "%s\n" (ExtString.String.join "\n" (print_errors errs))
  | Ok (program, trace) ->
     if !show_trace then
       printf "%s\n" (ExtString.String.join sep (print_trace trace))
     else
       printf "%s\n" program;;
