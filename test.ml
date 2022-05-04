open Compile
open Runner
open Lexing
open Printf
open Assembly
open OUnit2
open Pretty
open Exprs
open Phases
open Errors
open Graph

let defaultALLOC = Register

let t ?(alloc = defaultALLOC) name program input expected =
  name >:: test_run ~args:[] ~std_input:input alloc program name expected

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected

let tgc ?(alloc = defaultALLOC) ?(no_builtins = false) name heap_size program input expected =
  name
  >:: test_run ~no_builtins
        ~args:[string_of_int heap_size]
        ~std_input:input alloc program name expected

let tvg ?(alloc = defaultALLOC) name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input alloc program name expected

let tvgc ?(alloc = defaultALLOC) name heap_size program input expected =
  name
  >:: test_run_valgrind ~args:[string_of_int heap_size] ~std_input:input alloc program name expected

let te ?(alloc = defaultALLOC) name program input expected =
  name >:: test_err ~args:[] ~std_input:input alloc program name expected

let tgce ?(alloc = defaultALLOC) ?(no_builtins = false) name heap_size program input expected =
  name
  >:: test_err ~no_builtins
        ~args:[string_of_int heap_size]
        ~std_input:input alloc program name expected

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal (untagP expected) (untagP (parse_string name program)) ~printer:string_of_program

let t_prog (name : string) (value : 'a program) (expected : 'a program) =
  name >:: fun _ -> assert_equal expected value ~printer:string_of_program

let teq name actual expected = name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)

let t_asm_list name value expected = name >:: fun _ -> assert_equal expected value ~printer:to_asm

let t_any name value expected = name >:: fun _ -> assert_equal expected value ~printer:ExtLib.dump

let t_ice_error (name : string) (error_thunk : unit -> 'a) (error_msg : string) : OUnit2.test =
  name >:: fun _ -> assert_raises (InternalCompilerError error_msg) error_thunk

let t_nye_error (name : string) (error_thunk : unit -> 'a) (error_msg : string) : OUnit2.test =
  name >:: fun _ -> assert_raises (NotYetImplemented error_msg) error_thunk

let tfvs name program expected =
  name
  >:: fun _ ->
  let ast = tag (parse_string name program) in
  let ast, stbl = gensymtbl ast in
  let anfed = anf ast stbl in
  match anfed with
  | AProgram (body, _) ->
      let vars = free_vars body in
      let c = Stdlib.compare in
      let str_list_print strs = "[" ^ ExtString.String.join ", " strs ^ "]" in
      assert_equal (List.sort c expected) (List.sort c vars) ~printer:str_list_print

let tfvs_cache (name : string) (program : string) (expected : (string list * tag) aprogram) =
  name
  >:: fun _ ->
  let desugared = desugar (parse_string name program) in
  let ast, stbl = gensymtbl (tag desugared) in
  let anfed = anf ast stbl in
  let actual = fvs_aprog_tolist (free_vars_cache (atag anfed)) in
  let tag_printer (fvs, tag) =
    " (["
    ^ List.fold_left (fun fv prev_string -> fv ^ "," ^ prev_string) "" fvs
    ^ "]" ^ sprintf ", %d" tag ^ ")"
  in
  let aprogram_printer p = string_of_aprogram_with 100 tag_printer p in
  assert_equal expected actual ~printer:aprogram_printer

(* Runs the given program through desugar and compares the environment produced to the expected environment *)
let tdesug name program expected =
  let parsed_prog = Runner.parse_string name program in
  let actual = desugar (untagP parsed_prog) in
  t_prog name actual expected

(* Runs the given program through naive_stack_allocation and compares the environment produced to the expected environment *)
(* NOTE: by default it does not create native closures *)
let talloc ?(no_builtins = true) name program expected_envt =
  let parsed_prog = Runner.parse_string name program in
  let sourcespan_prog = if no_builtins then parsed_prog else add_native_lambdas parsed_prog in
  let ast, stbl = gensymtbl (rename_and_tag (tag (desugar sourcespan_prog))) in
  let _, actual_envt = naive_stack_allocation (free_vars_cache (atag (anf ast stbl))) in
  t_any name actual_envt expected_envt

(* Runs the given program through register_allocation and compares the environment produced to the expected environment *)
(* NOTE: by default it does not create native closures *)
let tralloc ?(no_builtins = true) name program expected_envt =
  let parsed_prog = Runner.parse_string name program in
  let sourcespan_prog = if no_builtins then parsed_prog else add_native_lambdas parsed_prog in
  let ast, stbl = gensymtbl (rename_and_tag (tag (desugar sourcespan_prog))) in
  let _, actual_envt = register_allocation (free_vars_cache (atag (anf ast stbl))) in
  let actual_envt_sorted =
    List.sort compare (List.map (fun (_, env) -> List.sort compare env) actual_envt)
  in
  let expected_envt_sorted =
    List.sort compare (List.map (fun (_, env) -> List.sort compare env) expected_envt)
  in
  t_any name actual_envt_sorted expected_envt_sorted

(* Runs the given program through interfere and compares the results using graph_to_dotgraph *)
let tinterf ?(remove = StringSet.empty) name program expected =
  let parsed_prog = Runner.parse_string name program in
  let ast, stbl = gensymtbl (rename_and_tag (tag (desugar parsed_prog))) in
  let actual =
    match free_vars_cache (atag (anf ast stbl)) with
    | AProgram (body, _) -> body
  in
  t_any name (graph_to_dotgraph (interfere actual StringSet.empty remove)) expected

(* Runs the given program through interfere, colors the graph and compares the environments *)
let tcgraph ?(remove = StringSet.empty) ?(env = []) name program expected =
  let parsed_prog = Runner.parse_string name program in
  let ast, stbl = gensymtbl (rename_and_tag (tag (desugar parsed_prog))) in
  let actual =
    match free_vars_cache (atag (anf ast stbl)) with
    | AProgram (body, _) -> body
  in
  t_any name (color_graph (interfere actual StringSet.empty remove) env) expected

(* Runs the given program through inferP and compares the results using infer_remove_clos_env *)
let tinfer name program expected =
  let parsed_prog = Runner.parse_string name program in
  let actual = infer_remove_clos_env (inferP (rename_and_tag (tag (desugar parsed_prog)))) in
  t_any name actual expected

(* Runs the given program through gensymtbl and compares the resulting symbol tables *)
let tgensym name program expected =
  let parsed_prog = Runner.parse_string name program in
  let _, tbl = gensymtbl (rename_and_tag (tag (desugar parsed_prog))) in
  t_any name tbl expected

(* Redefining fvc helpers to simplify testing *)
let fvc_A a = fvc_A a StringSet.empty

let fvc_C c = fvc_C c StringSet.empty

(* Runs the given program and checks that the result of well-formed is an Ok fallible of the same program *)
let twf_ok (name : string) (program : string) =
  name
  >:: fun _ ->
  let parsed_prog = Runner.parse_string name program in
  let actual = is_well_formed parsed_prog in
  match actual with
  | Ok actual_p -> assert_equal parsed_prog actual_p ~printer:string_of_program
  | Error errors -> assert_equal (Ok parsed_prog) actual ~printer:ExtLib.dump

(* Runs the given program and checks that the result of well-formed is an Error fallible with the expected errors *)
let twf_error (name : string) (program : string) (expected_errs : exn list) =
  name
  >:: fun _ ->
  let parsed_prog = Runner.parse_string name program in
  let actual = is_well_formed parsed_prog in
  match actual with
  | Ok actual_p -> assert_equal (Ok parsed_prog) actual ~printer:ExtLib.dump
  | Error actual_errors -> assert_equal expected_errs actual_errors ~printer:ExtLib.dump

let is_wf_suite =
  "is_wf_suite"
  >::: [ twf_ok "num" "1";
         twf_error "num_overflow" "9223372036854775100"
           [ Overflow
               ( 9223372036854775100L,
                 ( {pos_fname= "num_overflow"; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                   {pos_fname= "num_overflow"; pos_lnum= 1; pos_bol= 0; pos_cnum= 19} ) ) ];
         t_any "num underflow"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   ENumber
                     ( -9223372036854775100L,
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 20} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 20} ) ) ) )
           (Error
              [ Overflow
                  ( -9223372036854775100L,
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 20} ) ) ] );
         t_any "bool"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EBool
                     ( true,
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EBool
                     ( true,
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ) ) );
         t_any "unbound id"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EId
                     ( "x",
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ) ) )
           (Error
              [ UnboundId
                  ( "x",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ) ] );
         t_any "prim1 arith"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( Add1,
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 6} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( Add1,
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 6} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ) ) );
         t_any "prim1 not"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( Not,
                       EBool
                         ( false,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 2},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( Not,
                       EBool
                         ( false,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 2},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ) ) );
         t_any "prim1 tag check"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( IsBool,
                       ENumber
                         ( 4L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EPrim1
                     ( IsBool,
                       ENumber
                         ( 4L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ) );
         t_any "prim2 arith"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( Minus,
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ),
                       ENumber
                         ( 3L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( Minus,
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ),
                       ENumber
                         ( 3L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ) ) );
         t_any "prim2 bool"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( And,
                       EBool
                         ( true,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ),
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( And,
                       EBool
                         ( true,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4} ) ),
                       ENumber
                         ( 5L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ) );
         t_any "if"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   EIf
                     ( EBool
                         ( true,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 3},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                       ENumber
                         ( 4L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10} ) ),
                       ENumber
                         ( 2L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   EIf
                     ( EBool
                         ( true,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 3},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ),
                       ENumber
                         ( 4L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10} ) ),
                       ENumber
                         ( 2L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ) ) );
         t_any "let shadow"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                           ENumber
                             ( 5L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ],
                       ELet
                         ( [ ( BName
                                 ( "x",
                                   false,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                               ENumber
                                 ( 3L,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ),
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ) ) )
           (Ok
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                           ENumber
                             ( 5L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ],
                       ELet
                         ( [ ( BName
                                 ( "x",
                                   false,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                               ENumber
                                 ( 3L,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ),
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ) ) );
         t_any "let nested duplicate and unbound"
           (is_well_formed
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                           ENumber
                             ( 5L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) );
                         ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 12} ) ),
                           ENumber
                             ( 3L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 15},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 16} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 16} ) ) ],
                       EId
                         ( "y",
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 20},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21} ) ) ) )
           (Error
              [ UnboundId
                  ( "y",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 20},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21} ) );
                DuplicateId
                  ( "x",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 12} ),
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ) ] );
         t_any "unbound_id"
           (is_well_formed (Runner.parse_string "" "a"))
           (Error
              [ UnboundId
                  ( "a",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 1} ) ) ] );
         t_any "let_unbound_rec"
           (is_well_formed (Runner.parse_string "" "let x = 1, x = x + 1 in x"))
           (Error
              [ DuplicateId
                  ( "x",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 12} ),
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ) ] );
         t_any "let_unbound_rec_nest"
           (is_well_formed (Runner.parse_string "" "let x = 1 in let x = x in x"))
           (Ok
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                           ENumber
                             ( 1L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ],
                       ELet
                         ( [ ( BName
                                 ( "x",
                                   false,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 18} ) ),
                               EId
                                 ( "x",
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ),
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 17},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ) ) );
         t_any "def fun call"
           (is_well_formed (Runner.parse_string "" "def f(x): x\n f(1)"))
           (Ok
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [ BName
                               ( "x",
                                 false,
                                 ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 6},
                                   {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11} ) ) ] ],
                   EApp
                     ( EId
                         ( "f",
                           ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 14} ) ),
                       [ ENumber
                           ( 1L,
                             ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 15},
                               {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 16} ) ) ],
                       Unknown,
                       ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 13},
                         {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 17} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 17} ) ) ) );
         t_any "unboun_fun"
           (is_well_formed (Runner.parse_string "" "def f(x): x\n g(1)"))
           (Error
              [ Errors.UnboundId
                  ( "g",
                    ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 13},
                      {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 14} ) ) ] );
         t_any "arity_fun"
           (is_well_formed (Runner.parse_string "" "def f(x): x\n f(1, 2)"))
           (Error
              [ Errors.Arity
                  ( 1,
                    2,
                    ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 13},
                      {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 20} ) ) ] );
         t_any "shadow_fun"
           (is_well_formed (Runner.parse_string "" "def f(x): x\n def f(x): x\n3"))
           (Ok
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [ BName
                               ( "x",
                                 false,
                                 ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 6},
                                   {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 7} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11} ) ) ];
                     [ DFun
                         ( "f",
                           [ BName
                               ( "x",
                                 false,
                                 ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 19},
                                   {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 20} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 23},
                                 {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 24} ) ),
                           ( {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 2; pos_bol= 12; pos_cnum= 24} ) ) ] ],
                   ENumber
                     ( 3L,
                       ( {pos_fname= ""; pos_lnum= 3; pos_bol= 25; pos_cnum= 25},
                         {pos_fname= ""; pos_lnum= 3; pos_bol= 25; pos_cnum= 26} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 3; pos_bol= 25; pos_cnum= 26} ) ) ) );
         t_any "mutual_rec without and"
           (is_well_formed (Runner.parse_string "" "def f(x): g(x)\ndef g(x): f(x)\n3"))
           (Error
              [ Errors.UnboundId
                  ( "g",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11} ) );
                Errors.UnboundId
                  ( "f",
                    ( {pos_fname= ""; pos_lnum= 2; pos_bol= 15; pos_cnum= 25},
                      {pos_fname= ""; pos_lnum= 2; pos_bol= 15; pos_cnum= 26} ) ) ] );
         t_any "lambda"
           (is_well_formed (Runner.parse_string "" "(lambda (x): x)"))
           (Ok
              (Program
                 ( [],
                   [],
                   ELambda
                     ( [ BName
                           ( "x",
                             false,
                             ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9},
                               {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 10} ) ) ],
                       EId
                         ( "x",
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 13},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 14} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 15} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 15} ) ) ) );
         t_any "lambda_let_shadow"
           (is_well_formed (Runner.parse_string "" "let x = 1 in (lambda (x): x)"))
           (Ok
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName
                             ( "x",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 5} ) ),
                           ENumber
                             ( 1L,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ],
                       ELambda
                         ( [ BName
                               ( "x",
                                 false,
                                 ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22},
                                   {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 23} ) ) ],
                           EId
                             ( "x",
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 12},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 28} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 28} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 28} ) ) ) );
         t_any "let rec lambda"
           (is_well_formed (Runner.parse_string "" "let rec f = (lambda (x): f(x)) in 3"))
           (Ok
              (Program
                 ( [],
                   [],
                   ELetRec
                     ( [ ( BName
                             ( "f",
                               false,
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                           ELambda
                             ( [ BName
                                   ( "x",
                                     false,
                                     ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 21},
                                       {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 22} ) ) ],
                               EApp
                                 ( EId
                                     ( "f",
                                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 25},
                                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26} ) ),
                                   [ EId
                                       ( "x",
                                         ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 27},
                                           {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 28} )
                                       ) ],
                                   Unknown,
                                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 25},
                                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 29} ) ),
                               ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 11},
                                 {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 30} ) ),
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 30} ) ) ],
                       ENumber
                         ( 3L,
                           ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 34},
                             {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 35} ) ),
                       ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                         {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 35} ) ),
                   ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 0},
                     {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 35} ) ) ) );
         t_any "let rec non-func"
           (is_well_formed (Runner.parse_string "" "let rec f = 20 in 3"))
           (Error
              [ Errors.LetRecNonFunction
                  ( BName
                      ( "f",
                        false,
                        ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                          {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ),
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 14} ) ) ] );
         t_any "let_rec_mutual_rec_bad"
           (is_well_formed
              (Runner.parse_string ""
                 "let rec f = (lambda (x): g(x)) in let rec g = (lambda (x): f(x))  in 3" ) )
           (Error
              [ Errors.UnboundId
                  ( "g",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 25},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 26} ) ) ] );
         t_any "let_rec_duplicate"
           (is_well_formed
              (Runner.parse_string "" "let rec f = (lambda (x): f(x)), f = (lambda (x): f(x))  in 3") )
           (Error
              [ Errors.DuplicateId
                  ( "f",
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 32},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 33} ),
                    ( {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 8},
                      {pos_fname= ""; pos_lnum= 1; pos_bol= 0; pos_cnum= 9} ) ) ] );
         twf_error "let_rec_struct_arity"
           "struct Posn = (x, y) in endstruct let rec s = (lambda (x): new Posn(x)) in s"
           [ Errors.StructArity
               ( 2,
                 1,
                 ( {Lexing.pos_fname= "let_rec_struct_arity"; pos_lnum= 1; pos_bol= 0; pos_cnum= 59},
                   {Lexing.pos_fname= "let_rec_struct_arity"; pos_lnum= 1; pos_bol= 0; pos_cnum= 70}
                 ) ) ];
         twf_error "let_rec_struct_arity2"
           "struct Posn = (x, y) in endstruct let rec s = (lambda (x, y, z): new Posn(x, y, z)) in \
            s"
           [ Errors.StructArity
               ( 2,
                 3,
                 ( {Lexing.pos_fname= "let_rec_struct_arity2"; pos_lnum= 1; pos_bol= 0; pos_cnum= 65},
                   {Lexing.pos_fname= "let_rec_struct_arity2"; pos_lnum= 1; pos_bol= 0; pos_cnum= 82}
                 ) ) ];
         twf_error "let_invalid_struct" "let s: Posn = 200 in s"
           [ Errors.UnboundStruct
               ( "Posn",
                 ( {Lexing.pos_fname= "let_invalid_struct"; pos_lnum= 1; pos_bol= 0; pos_cnum= 4},
                   {Lexing.pos_fname= "let_invalid_struct"; pos_lnum= 1; pos_bol= 0; pos_cnum= 11}
                 ) ) ];
         twf_error "let_struct_arity" "struct Posn = (x, y) in endstruct let s = new Posn(1) in s"
           [ Errors.StructArity
               ( 2,
                 1,
                 ( {Lexing.pos_fname= "let_struct_arity"; pos_lnum= 1; pos_bol= 0; pos_cnum= 42},
                   {Lexing.pos_fname= "let_struct_arity"; pos_lnum= 1; pos_bol= 0; pos_cnum= 53} )
               ) ];
         twf_error "let_struct_arity2"
           "struct Posn = (x, y) in endstruct let s = new Posn(1, 2, 3) in s"
           [ Errors.StructArity
               ( 2,
                 3,
                 ( {Lexing.pos_fname= "let_struct_arity2"; pos_lnum= 1; pos_bol= 0; pos_cnum= 42},
                   {Lexing.pos_fname= "let_struct_arity2"; pos_lnum= 1; pos_bol= 0; pos_cnum= 59} )
               ) ] ]

let rename_suite =
  "rename_suite"
  >::: [ t_any "print"
           (rename_and_tag
              (Program ([], [], EApp (EId ("print", 4), [ENumber (4L, 3)], Unknown, 2), 1)) )
           (Program ([], [], EApp (EId ("print", 4), [ENumber (4L, 3)], Native, 2), 1));
         t_any "snake"
           (rename_and_tag
              (Program ([], [], EApp (EId ("f", 4), [ENumber (4L, 3)], Unknown, 2), 1)) )
           (Program ([], [], EApp (EId ("f", 4), [ENumber (4L, 3)], Snake, 2), 1));
         t_any "snake bound"
           (rename_and_tag
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName ("f", false, 4),
                           ELambda ([BName ("x", false, 7)], EId ("x", 6), 5),
                           3 ) ],
                       EApp (EId ("f", 10), [ENumber (4L, 9)], Unknown, 8),
                       2 ),
                   1 ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ ( BName ("f_4", false, 4),
                        ELambda ([BName ("x_7", false, 7)], EId ("x_7", 6), 5),
                        3 ) ],
                    EApp (EId ("f_4", 10), [ENumber (4L, 9)], Snake, 8),
                    2 ),
                1 ) ) ]

let desugar_suite =
  "desugar_suite"
  >::: [ t_prog "number"
           (desugar (Program ([], [], ENumber (5L, ()), ())))
           (Program ([], [], ENumber (5L, ()), ()));
         t_prog "bool"
           (desugar (Program ([], [], EBool (true, ()), ())))
           (Program ([], [], EBool (true, ()), ()));
         t_prog "1+1"
           (desugar (Program ([], [], EPrim2 (Plus, ENumber (1L, ()), ENumber (1L, ()), ()), ())))
           (Program ([], [], EPrim2 (Plus, ENumber (1L, ()), ENumber (1L, ()), ()), ()));
         t_prog "1-1"
           (desugar (Program ([], [], EPrim2 (Minus, ENumber (1L, ()), ENumber (1L, ()), ()), ())))
           (Program ([], [], EPrim2 (Minus, ENumber (1L, ()), ENumber (1L, ()), ()), ()));
         t_prog "1*1"
           (desugar (Program ([], [], EPrim2 (Times, ENumber (1L, ()), ENumber (1L, ()), ()), ())))
           (Program ([], [], EPrim2 (Times, ENumber (1L, ()), ENumber (1L, ()), ()), ()));
         t_prog "and"
           (desugar (Program ([], [], EPrim2 (And, EBool (true, ()), EBool (false, ()), ()), ())))
           (Program
              ( [],
                [],
                EIf
                  ( EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                    EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                    () ),
                () ) );
         t_prog "or"
           (desugar (Program ([], [], EPrim2 (Or, EBool (false, ()), EBool (false, ()), ()), ())))
           (Program
              ( [],
                [],
                EIf
                  ( EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    () ),
                () ) );
         t_prog "and_short_print"
           (desugar
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( And,
                       EBool (false, ()),
                       EApp (EId ("print", ()), [ENumber (1L, ())], Unknown, ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                EIf
                  ( EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    EPrim1
                      ( Not,
                        EPrim1 (Not, EApp (EId ("print", ()), [ENumber (1L, ())], Unknown, ()), ()),
                        () ),
                    EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                    () ),
                () ) );
         t_prog "or_short_print"
           (desugar
              (Program
                 ( [],
                   [],
                   EPrim2
                     ( Or,
                       EBool (true, ()),
                       EApp (EId ("print", ()), [ENumber (1L, ())], Unknown, ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                EIf
                  ( EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                    EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                    EPrim1
                      ( Not,
                        EPrim1 (Not, EApp (EId ("print", ()), [ENumber (1L, ())], Unknown, ()), ()),
                        () ),
                    () ),
                () ) );
         t_prog "or_short_let"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ (BName ("x", false, ()), EBool (true, ()), ());
                         (BName ("y", false, ()), ENumber (4L, ()), ()) ],
                       EPrim2 (Or, EId ("x", ()), EId ("y", ()), ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ (BName ("x", false, ()), EBool (true, ()), ());
                      (BName ("y", false, ()), ENumber (4L, ()), ()) ],
                    EIf
                      ( EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EId ("y", ()), ()), ()),
                        () ),
                    () ),
                () ) );
         t_prog "and_short_let"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ (BName ("x", false, ()), EBool (true, ()), ());
                         (BName ("y", false, ()), ENumber (4L, ()), ()) ],
                       EPrim2 (And, EId ("x", ()), EId ("y", ()), ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ (BName ("x", false, ()), EBool (true, ()), ());
                      (BName ("y", false, ()), ENumber (4L, ()), ()) ],
                    EIf
                      ( EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EId ("y", ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                        () ),
                    () ),
                () ) );
         t_prog "greater"
           (desugar
              (Program ([], [], EPrim2 (Greater, ENumber (3L, ()), ENumber (4L, ()), ()), ())) )
           (Program ([], [], EPrim2 (Greater, ENumber (3L, ()), ENumber (4L, ()), ()), ()));
         t_prog "greatereq"
           (desugar
              (Program ([], [], EPrim2 (GreaterEq, ENumber (3L, ()), ENumber (3L, ()), ()), ())) )
           (Program ([], [], EPrim2 (GreaterEq, ENumber (3L, ()), ENumber (3L, ()), ()), ()));
         t_prog "less"
           (desugar (Program ([], [], EPrim2 (Less, ENumber (3L, ()), ENumber (4L, ()), ()), ())))
           (Program ([], [], EPrim2 (Less, ENumber (3L, ()), ENumber (4L, ()), ()), ()));
         t_prog "lesseq"
           (desugar (Program ([], [], EPrim2 (LessEq, ENumber (3L, ()), ENumber (3L, ()), ()), ())))
           (Program ([], [], EPrim2 (LessEq, ENumber (3L, ()), ENumber (3L, ()), ()), ()));
         t_prog "eq"
           (desugar (Program ([], [], EPrim2 (Eq, ENumber (3L, ()), ENumber (4L, ()), ()), ())))
           (Program ([], [], EPrim2 (Eq, ENumber (3L, ()), ENumber (4L, ()), ()), ()));
         t_prog "add1"
           (desugar (Program ([], [], EPrim1 (Add1, ENumber (10L, ()), ()), ())))
           (Program ([], [], EPrim1 (Add1, ENumber (10L, ()), ()), ()));
         t_prog "sub1"
           (desugar (Program ([], [], EPrim1 (Sub1, ENumber (10L, ()), ()), ())))
           (Program ([], [], EPrim1 (Sub1, ENumber (10L, ()), ()), ()));
         t_prog "is_num"
           (desugar (Program ([], [], EPrim1 (IsNum, ENumber (1L, ()), ()), ())))
           (Program ([], [], EPrim1 (IsNum, ENumber (1L, ()), ()), ()));
         t_prog "is_bool"
           (desugar (Program ([], [], EPrim1 (IsBool, ENumber (1L, ()), ()), ())))
           (Program ([], [], EPrim1 (IsBool, ENumber (1L, ()), ()), ()));
         t_prog "not"
           (desugar (Program ([], [], EPrim1 (Not, EBool (true, ()), ()), ())))
           (Program ([], [], EPrim1 (Not, EBool (true, ()), ()), ()));
         t_prog "let_x"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet ([(BName ("x", false, ()), ENumber (10L, ()), ())], EId ("x", ()), ()),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet ([(BName ("x", false, ()), ENumber (10L, ()), ())], EId ("x", ()), ()),
                () ) );
         t_prog "let_in_let_body"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [(BName ("x", false, ()), ENumber (10L, ()), ())],
                       ELet
                         ( [(BName ("y", false, ()), ENumber (10L, ()), ())],
                           EPrim2 (Times, EId ("x", ()), EId ("y", ()), ()),
                           () ),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [(BName ("x", false, ()), ENumber (10L, ()), ())],
                    ELet
                      ( [(BName ("y", false, ()), ENumber (10L, ()), ())],
                        EPrim2 (Times, EId ("x", ()), EId ("y", ()), ()),
                        () ),
                    () ),
                () ) );
         t_prog "let_y_gets_x"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ (BName ("x", false, ()), ENumber (5L, ()), ());
                         ( BName ("y", false, ()),
                           EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                           () ) ],
                       EId ("y", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ (BName ("x", false, ()), ENumber (5L, ()), ());
                      ( BName ("y", false, ()),
                        EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                        () ) ],
                    EId ("y", ()),
                    () ),
                () ) );
         t_prog "if"
           (desugar
              (Program ([], [], EIf (EBool (true, ()), ENumber (3L, ()), ENumber (4L, ()), ()), ())) )
           (Program ([], [], EIf (EBool (true, ()), ENumber (3L, ()), ENumber (4L, ()), ()), ()));
         t_prog "if_in_let_body"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ (BName ("x", false, ()), ENumber (5L, ()), ());
                         ( BName ("y", false, ()),
                           EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                           () ) ],
                       EId ("y", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ (BName ("x", false, ()), ENumber (5L, ()), ());
                      ( BName ("y", false, ()),
                        EPrim2 (Plus, EId ("x", ()), ENumber (5L, ()), ()),
                        () ) ],
                    EId ("y", ()),
                    () ),
                () ) );
         t_prog "let_tuple_binding"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BTuple
                             ( [ BName ("a", false, ());
                                 BName ("b", false, ());
                                 BName ("c", false, ()) ],
                               () ),
                           ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                           () ) ],
                       EId ("a", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ ( BName ("tup?1", false, ()),
                        ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                        () );
                      (BBlank (), EPrim2 (CheckSize, EId ("tup?1", ()), ENumber (3L, ()), ()), ());
                      ( BName ("a", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (0L, ()), ()),
                        () );
                      ( BName ("b", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (1L, ()), ()),
                        () );
                      ( BName ("c", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (2L, ()), ()),
                        () ) ],
                    EId ("a", ()),
                    () ),
                () ) );
         t_prog "let_tuple_binding_indirect"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName ("t", false, ()),
                           ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                           () );
                         ( BTuple
                             ( [ BName ("a", false, ());
                                 BName ("b", false, ());
                                 BName ("c", false, ()) ],
                               () ),
                           EId ("t", ()),
                           () ) ],
                       EId ("a", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ ( BName ("t", false, ()),
                        ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                        () );
                      (BName ("tup?1", false, ()), EId ("t", ()), ());
                      (BBlank (), EPrim2 (CheckSize, EId ("tup?1", ()), ENumber (3L, ()), ()), ());
                      ( BName ("a", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (0L, ()), ()),
                        () );
                      ( BName ("b", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (1L, ()), ()),
                        () );
                      ( BName ("c", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (2L, ()), ()),
                        () ) ],
                    EId ("a", ()),
                    () ),
                () ) );
         t_prog "let_tuple_binding_nested"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BTuple
                             ( [ BName ("a", false, ());
                                 BTuple ([BName ("b", false, ()); BName ("c", false, ())], ());
                                 BName ("d", false, ()) ],
                               () ),
                           ETuple
                             ( [ ENumber (1L, ());
                                 ETuple ([ENumber (2L, ()); ENumber (3L, ())], ());
                                 ENumber (4L, ()) ],
                               () ),
                           () ) ],
                       EId ("a", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ ( BName ("tup?1", false, ()),
                        ETuple
                          ( [ ENumber (1L, ());
                              ETuple ([ENumber (2L, ()); ENumber (3L, ())], ());
                              ENumber (4L, ()) ],
                            () ),
                        () );
                      (BBlank (), EPrim2 (CheckSize, EId ("tup?1", ()), ENumber (3L, ()), ()), ());
                      ( BName ("a", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (0L, ()), ()),
                        () );
                      ( BName ("tup?2", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (1L, ()), ()),
                        () );
                      (BBlank (), EPrim2 (CheckSize, EId ("tup?2", ()), ENumber (2L, ()), ()), ());
                      ( BName ("b", false, ()),
                        EGetItem (EId ("tup?2", ()), ENumber (0L, ()), ()),
                        () );
                      ( BName ("c", false, ()),
                        EGetItem (EId ("tup?2", ()), ENumber (1L, ()), ()),
                        () );
                      ( BName ("d", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (2L, ()), ()),
                        () ) ],
                    EId ("a", ()),
                    () ),
                () ) );
         t_prog "let_tuple_binding_blanks"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BTuple ([BName ("a", false, ()); BBlank (); BName ("c", false, ())], ()),
                           ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                           () ) ],
                       EId ("a", ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [ ( BName ("tup?1", false, ()),
                        ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                        () );
                      (BBlank (), EPrim2 (CheckSize, EId ("tup?1", ()), ENumber (3L, ()), ()), ());
                      ( BName ("a", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (0L, ()), ()),
                        () );
                      (BBlank (), EGetItem (EId ("tup?1", ()), ENumber (1L, ()), ()), ());
                      ( BName ("c", false, ()),
                        EGetItem (EId ("tup?1", ()), ENumber (2L, ()), ()),
                        () ) ],
                    EId ("a", ()),
                    () ),
                () ) );
         t_prog "desugar_within_tuple"
           (desugar
              (Program
                 ( [],
                   [],
                   ETuple
                     ([EPrim2 (And, EBool (true, ()), EBool (false, ()), ()); ENumber (3L, ())], ()),
                   () ) ) )
           (Program
              ( [],
                [],
                ETuple
                  ( [ EIf
                        ( EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                          EPrim1 (Not, EPrim1 (Not, EBool (false, ()), ()), ()),
                          EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                          () );
                      ENumber (3L, ()) ],
                    () ),
                () ) );
         t_prog "get_item"
           (desugar
              (Program
                 ( [],
                   [],
                   ELet
                     ( [ ( BName ("t", false, ()),
                           ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()),
                           () ) ],
                       EGetItem (EId ("t", ()), ENumber (0L, ()), ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [(BName ("t", false, ()), ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()), ())],
                    EGetItem (EId ("t", ()), ENumber (0L, ()), ()),
                    () ),
                () ) );
         t_prog "set_item"
           (desugar
              (Program
                 ( [],
                   [],
                   ESetItem
                     ( ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                       ENumber (2L, ()),
                       ETuple ([ENumber (3L, ()); ENumber (4L, ())], ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ESetItem
                  ( ETuple ([ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                    ENumber (2L, ()),
                    ETuple ([ENumber (3L, ()); ENumber (4L, ())], ()),
                    () ),
                () ) );
         t_prog "seq"
           (desugar
              (Program
                 ( [],
                   [],
                   ESeq (EBool (false, ()), ESeq (ENumber (3L, ()), EBool (true, ()), ()), ()),
                   () ) ) )
           (Program
              ( [],
                [],
                ELet
                  ( [(BBlank (), EBool (false, ()), ())],
                    ELet ([(BBlank (), ENumber (3L, ()), ())], EBool (true, ()), ()),
                    () ),
                () ) );
         t_prog "decl_with_and"
           (desugar
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [BName ("x", false, ())],
                           EPrim2 (And, EId ("x", ()), EBool (true, ()), ()),
                           () ) ] ],
                   EApp (EId ("f", ()), [EBool (false, ())], Unknown, ()),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ ( BName ("f", false, ()),
                        ELambda
                          ( [BName ("x", false, ())],
                            EIf
                              ( EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                                EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                                EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                                () ),
                            () ),
                        () ) ],
                    EApp (EId ("f", ()), [EBool (false, ())], Unknown, ()),
                    () ),
                () ) );
         t_prog "decl_with_or"
           (desugar
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [BName ("x", false, ())],
                           EPrim2 (Or, EId ("x", ()), EBool (true, ()), ()),
                           () ) ] ],
                   EApp (EId ("f", ()), [EBool (false, ())], Unknown, ()),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ ( BName ("f", false, ()),
                        ELambda
                          ( [BName ("x", false, ())],
                            EIf
                              ( EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                                EPrim1 (Not, EPrim1 (Not, EId ("x", ()), ()), ()),
                                EPrim1 (Not, EPrim1 (Not, EBool (true, ()), ()), ()),
                                () ),
                            () ),
                        () ) ],
                    EApp (EId ("f", ()), [EBool (false, ())], Unknown, ()),
                    () ),
                () ) );
         t_prog "and_function_app"
           (desugar
              (Program
                 ( [],
                   [[DFun ("f", [], EBool (true, ()), ()); DFun ("g", [], EBool (false, ()), ())]],
                   EPrim2
                     ( And,
                       EApp (EId ("f", ()), [], Unknown, ()),
                       EApp (EId ("g", ()), [], Unknown, ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ (BName ("f", false, ()), ELambda ([], EBool (true, ()), ()), ());
                      (BName ("g", false, ()), ELambda ([], EBool (false, ()), ()), ()) ],
                    EIf
                      ( EPrim1 (Not, EPrim1 (Not, EApp (EId ("f", ()), [], Unknown, ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EApp (EId ("g", ()), [], Unknown, ()), ()), ()),
                        EPrim1 (Not, EPrim1 (Not, EApp (EId ("f", ()), [], Unknown, ()), ()), ()),
                        () ),
                    () ),
                () ) );
         t_prog "or_function_app"
           (desugar
              (Program
                 ( [],
                   [[DFun ("f", [], EBool (true, ()), ())]; [DFun ("g", [], EBool (false, ()), ())]],
                   EPrim2
                     ( Or,
                       EApp (EId ("f", ()), [], Unknown, ()),
                       EApp (EId ("g", ()), [], Unknown, ()),
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [(BName ("f", false, ()), ELambda ([], EBool (true, ()), ()), ())],
                    ELetRec
                      ( [(BName ("g", false, ()), ELambda ([], EBool (false, ()), ()), ())],
                        EIf
                          ( EPrim1 (Not, EPrim1 (Not, EApp (EId ("f", ()), [], Unknown, ()), ()), ()),
                            EPrim1 (Not, EPrim1 (Not, EApp (EId ("f", ()), [], Unknown, ()), ()), ()),
                            EPrim1 (Not, EPrim1 (Not, EApp (EId ("g", ()), [], Unknown, ()), ()), ()),
                            () ),
                        () ),
                    () ),
                () ) );
         t_prog "decl_with_tuple_args"
           (desugar
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [BTuple ([BName ("a", false, ()); BName ("b", false, ())], ())],
                           EPrim2 (Plus, EId ("a", ()), EId ("b", ()), ()),
                           () ) ] ],
                   EApp
                     ( EId ("f", ()),
                       [ETuple ([ENumber (1L, ()); ENumber (2L, ())], ())],
                       Unknown,
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ ( BName ("f", false, ()),
                        ELambda
                          ( [BName ("arg_tup?1", false, ())],
                            ELet
                              ( [ (BName ("tup?2", false, ()), EId ("arg_tup?1", ()), ());
                                  ( BBlank (),
                                    EPrim2 (CheckSize, EId ("tup?2", ()), ENumber (2L, ()), ()),
                                    () );
                                  ( BName ("a", false, ()),
                                    EGetItem (EId ("tup?2", ()), ENumber (0L, ()), ()),
                                    () );
                                  ( BName ("b", false, ()),
                                    EGetItem (EId ("tup?2", ()), ENumber (1L, ()), ()),
                                    () ) ],
                                EPrim2 (Plus, EId ("a", ()), EId ("b", ()), ()),
                                () ),
                            () ),
                        () ) ],
                    EApp
                      ( EId ("f", ()),
                        [ETuple ([ENumber (1L, ()); ENumber (2L, ())], ())],
                        Unknown,
                        () ),
                    () ),
                () ) );
         t_prog "decl_with_tuple_args_nested"
           (desugar
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [ BTuple
                               ( [ BTuple ([BName ("a", false, ()); BName ("b", false, ())], ());
                                   BName ("c", false, ()) ],
                                 () ) ],
                           EPrim2 (Plus, EId ("a", ()), EId ("b", ()), ()),
                           () ) ] ],
                   EApp
                     ( EId ("f", ()),
                       [ ETuple
                           ( [ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()); ENumber (3L, ())],
                             () ) ],
                       Unknown,
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ ( BName ("f", false, ()),
                        ELambda
                          ( [BName ("arg_tup?1", false, ())],
                            ELet
                              ( [ (BName ("tup?2", false, ()), EId ("arg_tup?1", ()), ());
                                  ( BBlank (),
                                    EPrim2 (CheckSize, EId ("tup?2", ()), ENumber (2L, ()), ()),
                                    () );
                                  ( BName ("tup?3", false, ()),
                                    EGetItem (EId ("tup?2", ()), ENumber (0L, ()), ()),
                                    () );
                                  ( BBlank (),
                                    EPrim2 (CheckSize, EId ("tup?3", ()), ENumber (2L, ()), ()),
                                    () );
                                  ( BName ("a", false, ()),
                                    EGetItem (EId ("tup?3", ()), ENumber (0L, ()), ()),
                                    () );
                                  ( BName ("b", false, ()),
                                    EGetItem (EId ("tup?3", ()), ENumber (1L, ()), ()),
                                    () );
                                  ( BName ("c", false, ()),
                                    EGetItem (EId ("tup?2", ()), ENumber (1L, ()), ()),
                                    () ) ],
                                EPrim2 (Plus, EId ("a", ()), EId ("b", ()), ()),
                                () ),
                            () ),
                        () ) ],
                    EApp
                      ( EId ("f", ()),
                        [ ETuple
                            ( [ETuple ([ENumber (1L, ()); ENumber (2L, ())], ()); ENumber (3L, ())],
                              () ) ],
                        Unknown,
                        () ),
                    () ),
                () ) );
         t_prog "function_decl_with_blanks"
           (desugar
              (Program
                 ( [],
                   [ [ DFun
                         ( "f",
                           [BName ("a", false, ()); BBlank (); BName ("c", false, ())],
                           EPrim2 (Plus, EId ("a", ()), EId ("c", ()), ()),
                           () ) ] ],
                   EApp
                     ( EId ("f", ()),
                       [ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())],
                       Unknown,
                       () ),
                   () ) ) )
           (Program
              ( [],
                [],
                ELetRec
                  ( [ ( BName ("f", false, ()),
                        ELambda
                          ( [BName ("a", false, ()); BName ("_", false, ()); BName ("c", false, ())],
                            EPrim2 (Plus, EId ("a", ()), EId ("c", ()), ()),
                            () ),
                        () ) ],
                    EApp
                      ( EId ("f", ()),
                        [ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())],
                        Unknown,
                        () ),
                    () ),
                () ) );
         tdesug "struct def new" "struct Posn = (x, y) in let p = new Posn(1, 2) in p"
           (Program
              ( [DStruct ("Posn", [FName "x"; FName "y"], [], ())],
                [],
                ELet
                  ( [ ( BName ("p", false, ()),
                        EConstruct ("Posn", [ENumber (1L, ()); ENumber (2L, ())], ()),
                        () ) ],
                    EId ("p", ()),
                    () ),
                () ) );
         tdesug "two structs def"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in  let p = new Posn(1, 2), p3 = new \
            Posn(1, 2, 3) in p.x + p3.z"
           (Program
              ( [ DStruct ("Posn", [FName "x"; FName "y"], [], ());
                  DStruct ("Posn3D", [FName "x"; FName "y"; FName "z"], [], ()) ],
                [],
                ELet
                  ( [ ( BName ("p", false, ()),
                        EConstruct ("Posn", [ENumber (1L, ()); ENumber (2L, ())], ()),
                        () );
                      ( BName ("p3", false, ()),
                        EConstruct
                          ("Posn", [ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ())], ()),
                        () ) ],
                    EPrim2
                      (Plus, EGetter (EId ("p", ()), "x", ()), EGetter (EId ("p3", ()), "z", ()), ()),
                    () ),
                () ) );
         tdesug "struct method "
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct let p = new Posn(1, \
            2) in p.addUp()"
           (Program
              ( [ DStruct
                    ( "Posn",
                      [ FName "x";
                        FName "y";
                        FMethod
                          ( "addUp",
                            [],
                            ELambda
                              ( [],
                                EPrim2
                                  ( Plus,
                                    EGetter (EId ("self", ()), "x", ()),
                                    EGetter (EId ("self", ()), "y", ()),
                                    () ),
                                () ) ) ],
                      [],
                      () ) ],
                [],
                ELet
                  ( [ ( BName ("p", false, ()),
                        ELet
                          ( [ ( BStruct ("Posn?1", "Posn", ()),
                                EConstruct
                                  ("Posn", [ENumber (1L, ()); ENumber (2L, ()); ENil ()], ()),
                                () ) ],
                            ELetRec
                              ( [ ( BName ("tempcurry_addUp", false, ()),
                                    ELambda
                                      ( [BStruct ("self", "Posn", ())],
                                        ELambda
                                          ( [],
                                            EPrim2
                                              ( Plus,
                                                EGetter (EId ("self", ()), "x", ()),
                                                EGetter (EId ("self", ()), "y", ()),
                                                () ),
                                            () ),
                                        () ),
                                    () ) ],
                                ESeq
                                  ( ESetter
                                      ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                        "addUp",
                                        EApp
                                          ( EId ("tempcurry_addUp", ()),
                                            [EId ("Posn?1", ())],
                                            Snake,
                                            () ),
                                        () ),
                                    EId ("Posn?1", ()),
                                    () ),
                                () ),
                            () ),
                        () ) ],
                    EApp (EGetter (EId ("p", ()), "addUp", ()), [], Unknown, ()),
                    () ),
                () ) );
         tdesug "struct method new in method"
           "struct Posn = (x, y) in method addUp(): self.x + self.y method mult(m): new \
            Posn(self.x * m * self.addUp(), self.y * m * self.addUp()) endstruct\n\
            let p = new Posn(1, 2) in p.mult(4)"
           (Program
              ( [ DStruct
                    ( "Posn",
                      [ FName "x";
                        FName "y";
                        FMethod
                          ( "addUp",
                            [],
                            ELambda
                              ( [],
                                EPrim2
                                  ( Plus,
                                    EGetter (EId ("self", ()), "x", ()),
                                    EGetter (EId ("self", ()), "y", ()),
                                    () ),
                                () ) );
                        FMethod
                          ( "mult",
                            [BName ("m", false, ())],
                            ELambda
                              ( [BName ("m", false, ())],
                                ELet
                                  ( [ ( BStruct ("Posn?1", "Posn", ()),
                                        EConstruct
                                          ( "Posn",
                                            [ EPrim2
                                                ( Times,
                                                  EPrim2
                                                    ( Times,
                                                      EGetter (EId ("self", ()), "x", ()),
                                                      EId ("m", ()),
                                                      () ),
                                                  EApp
                                                    ( EGetter (EId ("self", ()), "addUp", ()),
                                                      [],
                                                      Unknown,
                                                      () ),
                                                  () );
                                              EPrim2
                                                ( Times,
                                                  EPrim2
                                                    ( Times,
                                                      EGetter (EId ("self", ()), "y", ()),
                                                      EId ("m", ()),
                                                      () ),
                                                  EApp
                                                    ( EGetter (EId ("self", ()), "addUp", ()),
                                                      [],
                                                      Unknown,
                                                      () ),
                                                  () );
                                              EGetter (EId ("self", ()), "addUp", ());
                                              EGetter (EId ("self", ()), "mult", ()) ],
                                            () ),
                                        () ) ],
                                    ELet
                                      ( [ ( BBlank (),
                                            ESetter
                                              ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                "mult",
                                                EApp
                                                  ( EId ("tempcurry_mult", ()),
                                                    [EId ("Posn?1", ())],
                                                    Snake,
                                                    () ),
                                                () ),
                                            () ) ],
                                        ELet
                                          ( [ ( BBlank (),
                                                ESetter
                                                  ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                    "addUp",
                                                    EApp
                                                      ( EId ("tempcurry_addUp", ()),
                                                        [EId ("Posn?1", ())],
                                                        Snake,
                                                        () ),
                                                    () ),
                                                () ) ],
                                            EId ("Posn?1", ()),
                                            () ),
                                        () ),
                                    () ),
                                () ) ) ],
                      [],
                      () ) ],
                [],
                ELet
                  ( [ ( BName ("p", false, ()),
                        ELet
                          ( [ ( BStruct ("Posn?2", "Posn", ()),
                                EConstruct
                                  ( "Posn",
                                    [ENumber (1L, ()); ENumber (2L, ()); ENil (); ENil ()],
                                    () ),
                                () ) ],
                            ELetRec
                              ( [ ( BName ("tempcurry_mult", false, ()),
                                    ELambda
                                      ( [BStruct ("self", "Posn", ())],
                                        ELambda
                                          ( [BName ("m", false, ())],
                                            ELet
                                              ( [ ( BStruct ("Posn?1", "Posn", ()),
                                                    EConstruct
                                                      ( "Posn",
                                                        [ EPrim2
                                                            ( Times,
                                                              EPrim2
                                                                ( Times,
                                                                  EGetter (EId ("self", ()), "x", ()),
                                                                  EId ("m", ()),
                                                                  () ),
                                                              EApp
                                                                ( EGetter
                                                                    (EId ("self", ()), "addUp", ()),
                                                                  [],
                                                                  Unknown,
                                                                  () ),
                                                              () );
                                                          EPrim2
                                                            ( Times,
                                                              EPrim2
                                                                ( Times,
                                                                  EGetter (EId ("self", ()), "y", ()),
                                                                  EId ("m", ()),
                                                                  () ),
                                                              EApp
                                                                ( EGetter
                                                                    (EId ("self", ()), "addUp", ()),
                                                                  [],
                                                                  Unknown,
                                                                  () ),
                                                              () );
                                                          EGetter (EId ("self", ()), "addUp", ());
                                                          EGetter (EId ("self", ()), "mult", ()) ],
                                                        () ),
                                                    () ) ],
                                                ELet
                                                  ( [ ( BBlank (),
                                                        ESetter
                                                          ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                            "mult",
                                                            EApp
                                                              ( EId ("tempcurry_mult", ()),
                                                                [EId ("Posn?1", ())],
                                                                Snake,
                                                                () ),
                                                            () ),
                                                        () ) ],
                                                    ELet
                                                      ( [ ( BBlank (),
                                                            ESetter
                                                              ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                                "addUp",
                                                                EApp
                                                                  ( EId ("tempcurry_addUp", ()),
                                                                    [EId ("Posn?1", ())],
                                                                    Snake,
                                                                    () ),
                                                                () ),
                                                            () ) ],
                                                        EId ("Posn?1", ()),
                                                        () ),
                                                    () ),
                                                () ),
                                            () ),
                                        () ),
                                    () );
                                  ( BName ("tempcurry_addUp", false, ()),
                                    ELambda
                                      ( [BStruct ("self", "Posn", ())],
                                        ELambda
                                          ( [],
                                            EPrim2
                                              ( Plus,
                                                EGetter (EId ("self", ()), "x", ()),
                                                EGetter (EId ("self", ()), "y", ()),
                                                () ),
                                            () ),
                                        () ),
                                    () ) ],
                                ESeq
                                  ( ESetter
                                      ( EAs (EId ("Posn?2", ()), "Posn", ()),
                                        "addUp",
                                        EApp
                                          ( EId ("tempcurry_addUp", ()),
                                            [EId ("Posn?2", ())],
                                            Snake,
                                            () ),
                                        () ),
                                    ESeq
                                      ( ESetter
                                          ( EAs (EId ("Posn?2", ()), "Posn", ()),
                                            "mult",
                                            EApp
                                              ( EId ("tempcurry_mult", ()),
                                                [EId ("Posn?2", ())],
                                                Snake,
                                                () ),
                                            () ),
                                        EId ("Posn?2", ()),
                                        () ),
                                    () ),
                                () ),
                            () ),
                        () ) ],
                    EApp (EGetter (EId ("p", ()), "mult", ()), [ENumber (4L, ())], Unknown, ()),
                    () ),
                () ) );
         tdesug "two structs with methods"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct struct Posn3D = (x, \
            y, z) in method convert(): new Posn(self.x, self.y) endstruct\n\
            let p = new Posn(1, 2), p3 = new Posn3D(1, 2, 3) in p.x + p3.z"
           (Program
              ( [ DStruct
                    ( "Posn",
                      [ FName "x";
                        FName "y";
                        FMethod
                          ( "addUp",
                            [],
                            ELambda
                              ( [],
                                EPrim2
                                  ( Plus,
                                    EGetter (EId ("self", ()), "x", ()),
                                    EGetter (EId ("self", ()), "y", ()),
                                    () ),
                                () ) ) ],
                      [],
                      () );
                  DStruct
                    ( "Posn3D",
                      [ FName "x";
                        FName "y";
                        FName "z";
                        FMethod
                          ( "convert",
                            [],
                            ELambda
                              ( [],
                                ELet
                                  ( [ ( BStruct ("Posn?1", "Posn", ()),
                                        EConstruct
                                          ( "Posn",
                                            [ EGetter (EId ("self", ()), "x", ());
                                              EGetter (EId ("self", ()), "y", ());
                                              ENil () ],
                                            () ),
                                        () ) ],
                                    ELetRec
                                      ( [ ( BName ("tempcurry_addUp", false, ()),
                                            ELambda
                                              ( [BStruct ("self", "Posn", ())],
                                                ELambda
                                                  ( [],
                                                    EPrim2
                                                      ( Plus,
                                                        EGetter (EId ("self", ()), "x", ()),
                                                        EGetter (EId ("self", ()), "y", ()),
                                                        () ),
                                                    () ),
                                                () ),
                                            () ) ],
                                        ESeq
                                          ( ESetter
                                              ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                "addUp",
                                                EApp
                                                  ( EId ("tempcurry_addUp", ()),
                                                    [EId ("Posn?1", ())],
                                                    Snake,
                                                    () ),
                                                () ),
                                            EId ("Posn?1", ()),
                                            () ),
                                        () ),
                                    () ),
                                () ) ) ],
                      [],
                      () ) ],
                [],
                ELet
                  ( [ ( BName ("p", false, ()),
                        ELet
                          ( [ ( BStruct ("Posn?2", "Posn", ()),
                                EConstruct
                                  ("Posn", [ENumber (1L, ()); ENumber (2L, ()); ENil ()], ()),
                                () ) ],
                            ELetRec
                              ( [ ( BName ("tempcurry_addUp", false, ()),
                                    ELambda
                                      ( [BStruct ("self", "Posn", ())],
                                        ELambda
                                          ( [],
                                            EPrim2
                                              ( Plus,
                                                EGetter (EId ("self", ()), "x", ()),
                                                EGetter (EId ("self", ()), "y", ()),
                                                () ),
                                            () ),
                                        () ),
                                    () ) ],
                                ESeq
                                  ( ESetter
                                      ( EAs (EId ("Posn?2", ()), "Posn", ()),
                                        "addUp",
                                        EApp
                                          ( EId ("tempcurry_addUp", ()),
                                            [EId ("Posn?2", ())],
                                            Snake,
                                            () ),
                                        () ),
                                    EId ("Posn?2", ()),
                                    () ),
                                () ),
                            () ),
                        () );
                      ( BName ("p3", false, ()),
                        ELet
                          ( [ ( BStruct ("Posn3D?3", "Posn3D", ()),
                                EConstruct
                                  ( "Posn3D",
                                    [ENumber (1L, ()); ENumber (2L, ()); ENumber (3L, ()); ENil ()],
                                    () ),
                                () ) ],
                            ELetRec
                              ( [ ( BName ("tempcurry_convert", false, ()),
                                    ELambda
                                      ( [BStruct ("self", "Posn3D", ())],
                                        ELambda
                                          ( [],
                                            ELet
                                              ( [ ( BStruct ("Posn?1", "Posn", ()),
                                                    EConstruct
                                                      ( "Posn",
                                                        [ EGetter (EId ("self", ()), "x", ());
                                                          EGetter (EId ("self", ()), "y", ());
                                                          ENil () ],
                                                        () ),
                                                    () ) ],
                                                ELetRec
                                                  ( [ ( BName ("tempcurry_addUp", false, ()),
                                                        ELambda
                                                          ( [BStruct ("self", "Posn", ())],
                                                            ELambda
                                                              ( [],
                                                                EPrim2
                                                                  ( Plus,
                                                                    EGetter
                                                                      (EId ("self", ()), "x", ()),
                                                                    EGetter
                                                                      (EId ("self", ()), "y", ()),
                                                                    () ),
                                                                () ),
                                                            () ),
                                                        () ) ],
                                                    ESeq
                                                      ( ESetter
                                                          ( EAs (EId ("Posn?1", ()), "Posn", ()),
                                                            "addUp",
                                                            EApp
                                                              ( EId ("tempcurry_addUp", ()),
                                                                [EId ("Posn?1", ())],
                                                                Snake,
                                                                () ),
                                                            () ),
                                                        EId ("Posn?1", ()),
                                                        () ),
                                                    () ),
                                                () ),
                                            () ),
                                        () ),
                                    () ) ],
                                ESeq
                                  ( ESetter
                                      ( EAs (EId ("Posn3D?3", ()), "Posn3D", ()),
                                        "convert",
                                        EApp
                                          ( EId ("tempcurry_convert", ()),
                                            [EId ("Posn3D?3", ())],
                                            Snake,
                                            () ),
                                        () ),
                                    EId ("Posn3D?3", ()),
                                    () ),
                                () ),
                            () ),
                        () ) ],
                    EPrim2
                      (Plus, EGetter (EId ("p", ()), "x", ()), EGetter (EId ("p3", ()), "z", ()), ()),
                    () ),
                () ) ) ]

let free_vars_suite =
  "free_vars_suite"
  >::: [ tfvs "number" "1" [];
         tfvs "bool" "true" [];
         tfvs "nil" "nil" [];
         tfvs "free_id" "x" ["x"];
         tfvs "if_free_vars" "if a: b else: c" ["a"; "b"; "c"];
         tfvs "if_free_vars_nested" "if (a || b): (c && d) else: (e || f)"
           ["a"; "b"; "c"; "d"; "e"; "f"];
         tfvs "if_no_free_vars" "if true: 100 else: 200" [];
         tfvs "prim1_free_vars" "add1(x)" ["x"];
         tfvs "print1_free_vars_nested" "sub1((x + y))" ["x"; "y"];
         tfvs "prim1_no_free_vars" "add1(100)" [];
         tfvs "prim2_free_vars" "x + y" ["x"; "y"];
         tfvs "primt2_free_vars_nested" "(a + b) - (c + d)" ["a"; "b"; "c"; "d"];
         tfvs "prim2_no_free_vars" "1 + 2" [];
         tfvs "lambda_free_vars" "(lambda (x, y): x + y + k)" ["k"];
         tfvs "lambda_only_free_vars" "(lambda : a + b)" ["a"; "b"];
         tfvs "lambda_free_vars_nested" "(lambda (x, y) : (a + x) && (b - y))" ["a"; "b"];
         tfvs "lambda_no_free_vars" "(lambda (x, y): x + y)" [];
         tfvs "app_free_vars" "func(x, y)" ["func"; "x"; "y"];
         tfvs "app_free_vars_nested" "fun((x + y), z)" ["fun"; "x"; "y"; "z"];
         tfvs "app_no_free_vars" "fun(1, 2, 3)" ["fun"];
         tfvs "tuple_free_vars" "(x, y, 1, 2)" ["x"; "y"];
         tfvs "tuple_free_vars_nested" "(x, y, (z), 1, 2)" ["x"; "y"; "z"];
         tfvs "tuple_no_free_vars" "(1, 2, 3)" [];
         tfvs "get_free_vars" "tup[a]" ["tup"; "a"];
         tfvs "get_free_vars_nested" "((1, 2, tup)[a])[b]" ["tup"; "a"; "b"];
         tfvs "get_no_free_vars" "(1, 2, 3)[2]" [];
         tfvs "set_free_vars" "tup[a] := b" ["tup"; "a"; "b"];
         tfvs "set_free_vars_nested" "((1, 2, tup)[a])[b] := (x + y)" ["tup"; "a"; "b"; "x"; "y"];
         tfvs "set_no_free_vars" "(1, 2, 3)[2] := 100" [];
         tfvs "let_no_free_vars" "let x = 1, y = 2 in x + y" [];
         tfvs "let_free_vars" "let x = y, z = 10 in x + y + z + a" ["y"; "a"];
         tfvs "let_lambda_free_var" "let x = 10, y = (lambda (z): x + z) in y(100)" [];
         tfvs "lambda_letrec"
           "(lambda (x, y): let rec k = (lambda (x2): x2 + p + k(3)) in k(y + g))" ["p"; "g"];
         tfvs "let_rec_2" "let rec g = (lambda (y): y + h(y)) in g(x)" ["h"; "x"];
         tfvs "let_rec_2" "let rec g = (lambda (y): y + h(y)) in g(x)" ["h"; "x"];
         tfvs "let_rec_self_recursive" "let rec f = (lambda : f()) in f()" [];
         tfvs "sequence_free_vars" "let x = y in x; y + z" ["y"; "z"] ]

let alloc_suite =
  "alloc_suite"
  >::: [ talloc "bool" "true" [(0, [])];
         talloc "num" "10" [(0, [])];
         talloc "prim1" "!(false)" [(0, [])];
         talloc "prim2_plus" "4 + 4" [(0, [])];
         talloc "prim2_times" "4 * 3" [(0, [])];
         talloc "true_or_false" "true || false"
           [ ( 0,
               [ ("unary_4", RegOffset (-8, RBP));
                 ("unary_3", RegOffset (-16, RBP));
                 ("unary_7", RegOffset (-24, RBP));
                 ("unary_10", RegOffset (-32, RBP)) ] ) ];
         talloc "false_and_4" "false && 4"
           [ ( 0,
               [ ("unary_4", RegOffset (-8, RBP));
                 ("unary_3", RegOffset (-16, RBP));
                 ("unary_7", RegOffset (-24, RBP));
                 ("unary_10", RegOffset (-32, RBP)) ] ) ];
         talloc "numeric_comp" "4 > 1" [(0, [])];
         talloc "simple_let" "let x = 4 in x" [(0, [("x_4", RegOffset (-8, RBP))])];
         talloc "let_multiple_bindings" "let x = 4, y = 5 in x + y"
           [(0, [("x_4", RegOffset (-8, RBP)); ("y_7", RegOffset (-16, RBP))])];
         talloc "let_in_let_body" "let x = 4 in let y = x + 1 in y"
           [(0, [("x_4", RegOffset (-8, RBP)); ("y_8", RegOffset (-16, RBP))])];
         talloc "let_in_let_binding" "let x = 5, y = (let x = 3 in x) in y"
           [ ( 0,
               [ ("x_4", RegOffset (-8, RBP));
                 ("x_10", RegOffset (-16, RBP));
                 ("y_7", RegOffset (-24, RBP)) ] ) ];
         talloc "nested_lets" "let x = 2 in let y = x in let z = y in z"
           [ ( 0,
               [ ("x_4", RegOffset (-8, RBP));
                 ("y_8", RegOffset (-16, RBP));
                 ("z_12", RegOffset (-24, RBP)) ] ) ];
         talloc "lets_nested_binding_and_body" "let y = 2, x = (let x = 3 in x) in let z = x in z"
           [ ( 0,
               [ ("y_4", RegOffset (-8, RBP));
                 ("x_10", RegOffset (-16, RBP));
                 ("x_7", RegOffset (-24, RBP));
                 ("z_15", RegOffset (-32, RBP)) ] ) ];
         talloc "if_in_let_body" "let x = true, y = 10, z = 5 in (if x: y else: z)"
           [ ( 0,
               [ ("x_4", RegOffset (-8, RBP));
                 ("y_7", RegOffset (-16, RBP));
                 ("z_10", RegOffset (-24, RBP)) ] ) ];
         talloc "if_in_let_binding" "let x = (if true: 3 else: 5) in x + 4"
           [(0, [("x_4", RegOffset (-8, RBP))])];
         talloc "function_def_one_arg" "def f(x): x\n\nf(5)"
           [(0, [("f_4", RegOffset (-8, RBP))]); (5, [("x_7", RegOffset (24, RBP))])];
         talloc "function_def_multiple_args" "def f(x, y): x + y\n\nf(5, 3)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             (6, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         talloc "multiple_function_defs_with_let_inside_def"
           "def f(x, y): x + y\ndef g(x, y, z): let h = 4 in h\n\nh()"
           [ (0, [("f_4", RegOffset (-8, RBP)); ("g_13", RegOffset (-16, RBP))]);
             ( 5,
               [ ("h_17", RegOffset (-16, RBP));
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (9, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         talloc "multiple_function_defs_with_let_inside_def_and_body"
           "def f(x, y): x + y\ndef g(x, y, z): let h = 4 in h\n\nlet x = 5 in f(x, x)"
           [ ( 0,
               [ ("f_4", RegOffset (-8, RBP));
                 ("g_13", RegOffset (-16, RBP));
                 ("x_25", RegOffset (-24, RBP)) ] );
             ( 9,
               [ ("h_17", RegOffset (-16, RBP));
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (13, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         talloc "def_with_if_inside"
           "def f(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\nf(1, 2)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 6,
               [ ("g_10", RegOffset (-8, RBP));
                 ("h_15", RegOffset (-16, RBP));
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         talloc "def_with_let_multiple_bindings"
           "def f(x, y, z): let g = 1 in let z = 5 in g\n\nlet x = 5 in x"
           [ (0, [("f_4", RegOffset (-8, RBP)); ("x_20", RegOffset (-16, RBP))]);
             ( 5,
               [ ("g_8", RegOffset (-8, RBP));
                 ("z_12", RegOffset (-16, RBP));
                 ("x_15", RegOffset (24, RBP));
                 ("y_16", RegOffset (32, RBP));
                 ("z_17", RegOffset (40, RBP)) ] ) ];
         talloc "complex_1"
           "def f(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\
            def g(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\n\
            let x = 1, y = 2 in f(x, y) + g(x, y)"
           [ ( 0,
               [ ("f_4", RegOffset (-8, RBP));
                 ("g_22", RegOffset (-16, RBP));
                 ("x_40", RegOffset (-24, RBP));
                 ("y_43", RegOffset (-32, RBP));
                 ("app_46", RegOffset (-40, RBP));
                 ("app_50", RegOffset (-48, RBP)) ] );
             ( 20,
               [ ("g_28", RegOffset (-16, RBP));
                 ("h_33", RegOffset (-24, RBP));
                 ("x_36", RegOffset (24, RBP));
                 ("y_37", RegOffset (32, RBP)) ] );
             ( 29,
               [ ("g_10", RegOffset (-8, RBP));
                 ("h_15", RegOffset (-16, RBP));
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         talloc "tup_creation" "let t = (1, 2, 3) in t" [(0, [("t_4", RegOffset (-8, RBP))])];
         talloc "multiple_tup_creation" "let t = (1, 2, 3), y = (3, 4, 5) in y"
           [(0, [("t_4", RegOffset (-8, RBP)); ("y_10", RegOffset (-16, RBP))])];
         talloc "tup_destruct" "let t = (1, 2, 3), a = t[0], b = t[1], c = t[2] in c"
           [ ( 0,
               [ ("t_4", RegOffset (-8, RBP));
                 ("a_10", RegOffset (-16, RBP));
                 ("b_15", RegOffset (-24, RBP));
                 ("c_20", RegOffset (-32, RBP)) ] ) ];
         talloc "tup_creation_def" "def f(x): ((x + 1), (x - 1))\n\nf(4)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 5,
               [ ("binop_7", RegOffset (-8, RBP));
                 ("binop_10", RegOffset (-16, RBP));
                 ("x_13", RegOffset (24, RBP)) ] ) ];
         talloc "tup_def_destruct"
           "def f(x): let t = ((x + 1), (x - 1)), b = t[0], c = t[1] in b + c\n\nf(4)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 5,
               [ ("binop_10", RegOffset (-8, RBP));
                 ("binop_13", RegOffset (-16, RBP));
                 ("t_8", RegOffset (-24, RBP));
                 ("b_17", RegOffset (-32, RBP));
                 ("c_22", RegOffset (-40, RBP));
                 ("x_29", RegOffset (24, RBP)) ] ) ];
         talloc "tup_def_destruct_in_prog_body"
           "def f(x): let t = ((x + 1), (x - 1)), b = t[0], c = t[1] in b + c\n\n\
            let t = (1, 2), x = t[0], y = t[1] in f(x + y)"
           [ ( 0,
               [ ("f_4", RegOffset (-8, RBP));
                 ("t_32", RegOffset (-16, RBP));
                 ("x_37", RegOffset (-24, RBP));
                 ("y_42", RegOffset (-32, RBP));
                 ("binop_47", RegOffset (-40, RBP)) ] );
             ( 21,
               [ ("binop_10", RegOffset (-8, RBP));
                 ("binop_13", RegOffset (-16, RBP));
                 ("t_8", RegOffset (-24, RBP));
                 ("b_17", RegOffset (-32, RBP));
                 ("c_22", RegOffset (-40, RBP));
                 ("x_29", RegOffset (24, RBP)) ] ) ];
         talloc "tup_destruct_in_func_args"
           "def f((a, b), (c, d)): a + b + c + d\n\nlet t1 = (1, 2), t2 = (3, 4) in f(t1, t2)"
           [ ( 0,
               [ ("f_4", RegOffset (-8, RBP));
                 ("t1_54", RegOffset (-16, RBP));
                 ("t2_59", RegOffset (-24, RBP)) ] );
             ( 14,
               [ ("tup?3_8", RegOffset (-8, RBP));
                 ("a_16", RegOffset (-16, RBP));
                 ("b_21", RegOffset (-24, RBP));
                 ("tup?4_26", RegOffset (-32, RBP));
                 ("c_34", RegOffset (-40, RBP));
                 ("d_39", RegOffset (-48, RBP));
                 ("binop_45", RegOffset (-56, RBP));
                 ("binop_44", RegOffset (-64, RBP));
                 ("arg_tup?2_50", RegOffset (24, RBP));
                 ("arg_tup?1_51", RegOffset (32, RBP)) ] ) ];
         talloc "blank_in_def" "def f(x, _, _): x\n\nf(5, 1, 2)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 7,
               [ ("x_7", RegOffset (24, RBP));
                 ("__8", RegOffset (32, RBP));
                 ("__9", RegOffset (40, RBP)) ] ) ];
         talloc "blank_in_def_tup" "def f(x, (y, _), _): x + y\n\nf(1, (2, 3), 4)"
           [ (0, [("f_4", RegOffset (-8, RBP)); ("tup_33", RegOffset (-16, RBP))]);
             ( 11,
               [ ("tup?2_8", RegOffset (-8, RBP));
                 ("y_16", RegOffset (-16, RBP));
                 ("x_28", RegOffset (24, RBP));
                 ("arg_tup?1_29", RegOffset (32, RBP));
                 ("__30", RegOffset (40, RBP)) ] ) ];
         talloc "sequence" "let x = 4 in x; let y = 4 in y"
           [(0, [("x_4", RegOffset (-8, RBP)); ("y_12", RegOffset (-16, RBP))])];
         talloc "sequence_with_lets"
           "let x = 4, y = 5, z = 10 in x + y + z; let a = 1, b = 2, c = 3 in a + b + c"
           [ ( 0,
               [ ("x_4", RegOffset (-8, RBP));
                 ("y_7", RegOffset (-16, RBP));
                 ("z_10", RegOffset (-24, RBP));
                 ("binop_16", RegOffset (-32, RBP));
                 ("a_22", RegOffset (-40, RBP));
                 ("b_25", RegOffset (-48, RBP));
                 ("c_28", RegOffset (-56, RBP));
                 ("binop_31", RegOffset (-64, RBP)) ] ) ];
         talloc "lambda_lit_one_arg_simple" "(lambda (x): x)"
           [(0, []); (1, [("x_4", RegOffset (24, RBP))])];
         talloc "lambda_lit_fv" "let y = 3 in (lambda (x): x + y)"
           [ (0, [("y_4", RegOffset (-8, RBP))]);
             (2, [("x_10", RegOffset (24, RBP)); ("y_4", RegOffset (-8, RBP))]) ];
         talloc "lambda_empty_lit" "(lambda : 1)" [(0, []); (1, [])];
         talloc "two_lambdas" "let f = (lambda (x): x + 1), g = (lambda (x): x + 2) in f(1) + g(3)"
           [ ( 0,
               [ ("f_4", RegOffset (-8, RBP));
                 ("g_11", RegOffset (-16, RBP));
                 ("app_18", RegOffset (-24, RBP));
                 ("app_21", RegOffset (-32, RBP)) ] );
             (14, [("x_16", RegOffset (24, RBP))]);
             (18, [("x_9", RegOffset (24, RBP))]) ];
         talloc "let_in_lambda"
           "let f = (lambda (x, y): let x = x + 1, y = y + 1 in y + x) in f(4, 4)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 6,
               [ ("x_8", RegOffset (-16, RBP));
                 ("y_13", RegOffset (-24, RBP));
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP)) ] ) ];
         talloc "lambda_in_lambda_fv" "(lambda (x): (lambda (y): y + x)(5))(4)"
           [ (0, [("lam_4", RegOffset (-8, RBP))]);
             (5, [("lam_7", RegOffset (-16, RBP)); ("x_12", RegOffset (24, RBP))]);
             (10, [("y_11", RegOffset (24, RBP)); ("x_12", RegOffset (-8, RBP))]) ];
         talloc "letrec_in_letrec_recursive"
           "let rec f = (lambda (n): let rec g = (lambda (i): if n <= 1: i else: f(i - 1) ) in \
            g(n)) in f(10)"
           [ (0, [("f_4", RegOffset (-8, RBP))]);
             ( 5,
               [ ("g_8", RegOffset (-8, RBP));
                 ("n_24", RegOffset (24, RBP));
                 ("f_4", RegOffset (-8, RBP)) ] );
             ( 10,
               [ ("binop_11", RegOffset (-8, RBP));
                 ("binop_16", RegOffset (-16, RBP));
                 ("i_20", RegOffset (24, RBP));
                 ("f_4", RegOffset (-16, RBP));
                 ("n_24", RegOffset (-8, RBP)) ] ) ] ]

let compile_fun_suite =
  "compile_fun_suite"
  >::: [ t_any "num"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CImmExpr (ImmNum (1L, 1)))))
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [IMov (Reg RAX, Const 2L)],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "true"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CImmExpr (ImmBool (true, 1)))))
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [IMov (Reg RAX, HexConst (-1L))],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_ice_error "id not in env"
           (fun () ->
             compile_fun "blah" [] (fvc_A (ACExpr (CImmExpr (ImmId ("x", 1))))) [(0, [])] 8L )
           "Name \"x\" not found";
         t_any "id in env"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CImmExpr (ImmId ("x#3", 2)))))
              [(0, [("x#3", RegOffset (-8, RBP))])]
              8L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 8L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L) ],
             [IMov (Reg RAX, RegOffset (-8, RBP))],
             [IAdd (Reg RSP, Const 8L); IPop (Reg RBP); IRet] );
         t_any "add1"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CPrim1 (Add1, ImmNum (5L, 2), 1))))
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [ IMov (Reg RAX, Const 10L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 10L);
               IAdd (Reg RAX, Const 2L);
               IJo (Label "?err_overflow") ],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "isbool"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CPrim1 (IsBool, ImmNum (4L, 2), 1))))
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [ IMov (Reg RAX, Const 8L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               ISete (Reg AL);
               IShl (Reg RAX, Const 63L);
               IMov (Reg R11, HexConst 9223372036854775807L);
               IOr (Reg RAX, Reg R11) ],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "prim2 simple"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CPrim2 (Plus, ImmNum (2L, 3), ImmNum (5L, 2), 1))))
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [ IMov (Reg RAX, Const 4L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 10L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 4L);
               IAdd (Reg RAX, Const 10L);
               IJo (Label "?err_overflow") ],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "let x"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet ("x#3", CImmExpr (ImmNum (5L, 3)), ACExpr (CImmExpr (ImmId ("x#3", 2))), 1)) )
              [(0, [("x#3", RegOffset (-8, RBP))])]
              8L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 8L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 10L);
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP)) ],
             [IAdd (Reg RSP, Const 8L); IPop (Reg RBP); IRet] );
         t_any "lets"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "x#3",
                      CImmExpr (ImmNum (5L, 7)),
                      ALet
                        ( "y#5",
                          CImmExpr (ImmNum (4L, 6)),
                          ALet
                            ( "z#7",
                              CImmExpr (ImmNum (3L, 5)),
                              ACExpr (CImmExpr (ImmId ("x#3", 4))),
                              3 ),
                          2 ),
                      1 ) ) )
              [ ( 0,
                  [ ("x#3", RegOffset (-8, RBP));
                    ("y#5", RegOffset (-16, RBP));
                    ("z#7", RegOffset (-24, RBP)) ] ) ]
              32L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 32L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (24, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 10L);
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, Const 8L);
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, Const 6L);
               IMov (RegOffset (-24, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP)) ],
             [IAdd (Reg RSP, Const 32L); IPop (Reg RBP); IRet] );
         t_any "prim2 nested"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "binop_5",
                      CPrim2 (Plus, ImmNum (5L, 11), ImmNum (3L, 10), 9),
                      ALet
                        ( "binop_3",
                          CPrim2 (Times, ImmId ("binop_5", 8), ImmNum (3L, 7), 6),
                          ACExpr (CPrim2 (Plus, ImmId ("binop_3", 5), ImmNum (2L, 4), 3)),
                          2 ),
                      1 ) ) )
              [(0, [("binop_5", RegOffset (-8, RBP)); ("binop_3", RegOffset (-16, RBP))])]
              16L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 16L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 10L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 6L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 10L);
               IAdd (Reg RAX, Const 6L);
               IJo (Label "?err_overflow");
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 6L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (-8, RBP));
               ISar (Reg RAX, Const 1L);
               IMul (Reg RAX, Const 6L);
               IJo (Label "?err_overflow");
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 4L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAdd (Reg RAX, Const 4L);
               IJo (Label "?err_overflow") ],
             [IAdd (Reg RSP, Const 16L); IPop (Reg RBP); IRet] );
         t_any "printStack"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "binop_2",
                      CPrim2 (Plus, ImmNum (2L, 6), ImmNum (2L, 5), 4),
                      ACExpr (CPrim1 (PrintStack, ImmId ("binop_2", 3), 2)),
                      1 ) ) )
              [(0, [("binop_2", RegOffset (-8, RBP))])]
              16L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 16L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 4L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 4L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, Const 4L);
               IAdd (Reg RAX, Const 4L);
               IJo (Label "?err_overflow");
               IMov (RegOffset (-8, RBP), Reg RAX);
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IMov (Reg RDI, Reg RAX);
               IMov (Reg RSI, Reg RBP);
               IMov (Reg RDX, Reg RSP);
               IMov (Reg RCX, Const 0L);
               ICall (Label "?print_stack");
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10) ],
             [IAdd (Reg RSP, Const 16L); IPop (Reg RBP); IRet] );
         t_any "if"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ACExpr
                    (CIf
                       ( ImmBool (true, 4),
                         ACExpr (CImmExpr (ImmNum (4L, 3))),
                         ACExpr (CImmExpr (ImmNum (20L, 2))),
                         1 ) ) ) )
              [(0, [])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [ IMov (Reg RAX, HexConst (-1L));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_if_not_bool");
               IMov (Reg RAX, HexConst (-1L));
               IMov (Reg R11, HexConst (-1L));
               ICmp (Reg RAX, Reg R11);
               IJne (Label "else_if_1");
               ILabel "then_if_1";
               IMov (Reg RAX, Const 8L);
               IJmp (Label "done_if_1");
               ILabel "else_if_1";
               IMov (Reg RAX, Const 40L);
               ILabel "done_if_1" ],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "desugared and"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "unary_9",
                      CPrim1 (Not, ImmBool (true, 18), 17),
                      ALet
                        ( "unary_8",
                          CPrim1 (Not, ImmId ("unary_9", 16), 15),
                          ACExpr
                            (CIf
                               ( ImmId ("unary_8", 14),
                                 ALet
                                   ( "unary_6",
                                     CPrim1 (Not, ImmBool (false, 13), 12),
                                     ACExpr (CPrim1 (Not, ImmId ("unary_6", 11), 10)),
                                     9 ),
                                 ALet
                                   ( "unary_3",
                                     CPrim1 (Not, ImmBool (true, 8), 7),
                                     ACExpr (CPrim1 (Not, ImmId ("unary_3", 6), 5)),
                                     4 ),
                                 3 ) ),
                          2 ),
                      1 ) ) )
              [ ( 0,
                  [ ("unary_9", RegOffset (-8, RBP));
                    ("unary_8", RegOffset (-16, RBP));
                    ("unary_6", RegOffset (-24, RBP));
                    ("unary_3", RegOffset (-32, RBP)) ] ) ]
              32L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 32L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (24, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, HexConst (-1L));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, HexConst (-1L));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-8, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_if_not_bool");
               IMov (Reg RAX, RegOffset (-16, RBP));
               IMov (Reg R11, HexConst (-1L));
               ICmp (Reg RAX, Reg R11);
               IJne (Label "else_if_3");
               ILabel "then_if_3";
               IMov (Reg RAX, HexConst 9223372036854775807L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-24, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-24, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-24, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IJmp (Label "done_if_3");
               ILabel "else_if_3";
               IMov (Reg RAX, HexConst (-1L));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, HexConst (-1L));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-32, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-32, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-32, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               ILabel "done_if_3" ],
             [IAdd (Reg RSP, Const 32L); IPop (Reg RBP); IRet] );
         t_any "desugared or"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "unary_9",
                      CPrim1 (Not, ImmBool (false, 18), 17),
                      ALet
                        ( "unary_8",
                          CPrim1 (Not, ImmId ("unary_9", 16), 15),
                          ACExpr
                            (CIf
                               ( ImmId ("unary_8", 14),
                                 ALet
                                   ( "unary_6",
                                     CPrim1 (Not, ImmBool (false, 13), 12),
                                     ACExpr (CPrim1 (Not, ImmId ("unary_6", 11), 10)),
                                     9 ),
                                 ALet
                                   ( "unary_3",
                                     CPrim1 (Not, ImmNum (40L, 8), 7),
                                     ACExpr (CPrim1 (Not, ImmId ("unary_3", 6), 5)),
                                     4 ),
                                 3 ) ),
                          2 ),
                      1 ) ) )
              [ ( 0,
                  [ ("unary_9", RegOffset (-8, RBP));
                    ("unary_8", RegOffset (-16, RBP));
                    ("unary_6", RegOffset (-24, RBP));
                    ("unary_3", RegOffset (-32, RBP)) ] ) ]
              32L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 32L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (24, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, HexConst 9223372036854775807L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-8, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_if_not_bool");
               IMov (Reg RAX, RegOffset (-16, RBP));
               IMov (Reg R11, HexConst (-1L));
               ICmp (Reg RAX, Reg R11);
               IJne (Label "else_if_3");
               ILabel "then_if_3";
               IMov (Reg RAX, HexConst 9223372036854775807L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-24, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-24, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-24, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IJmp (Label "done_if_3");
               ILabel "else_if_3";
               IMov (Reg RAX, Const 80L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, Const 80L);
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-32, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-32, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-32, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               ILabel "done_if_3" ],
             [IAdd (Reg RSP, Const 32L); IPop (Reg RBP); IRet] );
         t_ice_error "non-desugared and"
           (fun () ->
             compile_fun "blah" []
               (fvc_A (ACExpr (CPrim2 (And, ImmBool (true, 3), ImmBool (true, 2), 1))))
               [(0, [])]
               0L )
           "Impossible: non-desugared primitive operation";
         t_ice_error "non-desugared or"
           (fun () ->
             compile_fun "blah" []
               (fvc_A (ACExpr (CPrim2 (Or, ImmBool (true, 3), ImmBool (true, 2), 1))))
               [(0, [])]
               0L )
           "Impossible: non-desugared primitive operation";
         t_any "numeric comp"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "binop_14",
                      CPrim2 (Less, ImmNum (4L, 30), ImmNum (6L, 29), 28),
                      ALet
                        ( "unary_13",
                          CPrim1 (Not, ImmId ("binop_14", 27), 26),
                          ALet
                            ( "unary_12",
                              CPrim1 (Not, ImmId ("unary_13", 25), 24),
                              ALet
                                ( "if_3",
                                  CIf
                                    ( ImmId ("unary_12", 23),
                                      ALet
                                        ( "unary_10",
                                          CPrim1 (Not, ImmNum (6L, 22), 21),
                                          ACExpr (CPrim1 (Not, ImmId ("unary_10", 20), 19)),
                                          18 ),
                                      ALet
                                        ( "binop_6",
                                          CPrim2 (Less, ImmNum (4L, 17), ImmNum (6L, 16), 15),
                                          ALet
                                            ( "unary_5",
                                              CPrim1 (Not, ImmId ("binop_6", 14), 13),
                                              ACExpr (CPrim1 (Not, ImmId ("unary_5", 12), 11)),
                                              10 ),
                                          9 ),
                                      8 ),
                                  ACExpr (CPrim2 (GreaterEq, ImmId ("if_3", 7), ImmNum (3L, 6), 5)),
                                  4 ),
                              3 ),
                          2 ),
                      1 ) ) )
              [ ( 0,
                  [ ("binop_14", RegOffset (-8, RBP));
                    ("unary_13", RegOffset (-16, RBP));
                    ("unary_12", RegOffset (-24, RBP));
                    ("if_3", RegOffset (-32, RBP));
                    ("unary_10", RegOffset (-40, RBP));
                    ("binop_6", RegOffset (-48, RBP));
                    ("unary_5", RegOffset (-56, RBP)) ] ) ]
              64L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 64L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (24, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (32, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (40, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (48, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (56, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 8L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, Const 12L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, Const 8L);
               IMov (Reg R11, Const 12L);
               ICmp (Reg RAX, Reg R11);
               IMov (Reg RAX, HexConst (-1L));
               IJl (Label "done_less_28");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               ILabel "done_less_28";
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-8, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-16, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-24, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-24, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_if_not_bool");
               IMov (Reg RAX, RegOffset (-24, RBP));
               IMov (Reg R11, HexConst (-1L));
               ICmp (Reg RAX, Reg R11);
               IJne (Label "else_if_8");
               ILabel "then_if_8";
               IMov (Reg RAX, Const 12L);
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, Const 12L);
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-40, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-40, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-40, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IJmp (Label "done_if_8");
               ILabel "else_if_8";
               IMov (Reg RAX, Const 8L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, Const 12L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, Const 8L);
               IMov (Reg R11, Const 12L);
               ICmp (Reg RAX, Reg R11);
               IMov (Reg RAX, HexConst (-1L));
               IJl (Label "done_less_15");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               ILabel "done_less_15";
               IMov (RegOffset (-48, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-48, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-48, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               IMov (RegOffset (-56, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-56, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 7L);
               IJne (Label "?err_logic_not_bool");
               IMov (Reg RAX, RegOffset (-56, RBP));
               IMov (Reg R11, HexConst (-9223372036854775808L));
               IXor (Reg RAX, Reg R11);
               ILabel "done_if_8";
               IMov (RegOffset (-32, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-32, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, Const 6L);
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_comp_not_num");
               IMov (Reg RAX, RegOffset (-32, RBP));
               IMov (Reg R11, Const 6L);
               ICmp (Reg RAX, Reg R11);
               IMov (Reg RAX, HexConst (-1L));
               IJge (Label "done_greatereq_5");
               IMov (Reg RAX, HexConst 9223372036854775807L);
               ILabel "done_greatereq_5" ],
             [IAdd (Reg RSP, Const 64L); IPop (Reg RBP); IRet] );
         t_any "lambda_lit"
           (compile_fun "our_code_starts_here" []
              (fvc_A (ACExpr (CLambda (["x_4"], ACExpr (CImmExpr (ImmId ("x_4", 2))), 1))))
              [(0, []); (1, [("x_4", RegOffset (24, RBP))])]
              0L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 0L) ],
             [ IJmp (Label "lambda_end_1");
               ILabel "lambda_1";
               IPush (Reg RBP);
               ILineComment "fvs space: 0";
               ILineComment "local var space: 0";
               IMov (Reg RBP, Reg RSP);
               ISub (Reg RSP, Const 0L);
               IMov (Reg R11, RegOffset (16, RBP));
               ISub (Reg R11, HexConst 5L);
               IMov (Reg RAX, RegOffset (24, RBP));
               IMov (Reg RSP, Reg RBP);
               IPop (Reg RBP);
               IRet;
               ILabel "lambda_end_1";
               ILineComment "Reserving 4 words";
               ICall (Label "?get_heap_end");
               ISub (Reg RAX, Const 32L);
               ICmp (Reg RAX, Reg R15);
               IJge (Label "$memcheck_1");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
               IMov (Reg RCX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
               IMov (Reg RDX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
               IMov (Reg RSI, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
               IMov (Reg RDI, Reg RAX);
               ICall (Label "?try_gc");
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10);
               IInstrComment
                 ( IMov (Reg R15, Reg RAX),
                   "assume gc success if returning here, so RAX holds the new heap_reg value" );
               ILabel "$memcheck_1";
               IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
               IMov (Reg R11, Label "lambda_1");
               IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
               IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L);
               ILineComment "free vars: 0";
               IMov (Reg RAX, Reg R15);
               IAdd (Reg RAX, HexConst 5L);
               IAdd (Reg R15, Const 32L) ],
             [IAdd (Reg RSP, Const 0L); IPop (Reg RBP); IRet] );
         t_any "lambda_fv_app"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALet
                    ( "y_4",
                      CImmExpr (ImmNum (5L, 10)),
                      ALet
                        ( "lam_8",
                          CLambda
                            ( ["x_12"],
                              ACExpr (CPrim2 (Plus, ImmId ("x_12", 9), ImmId ("y_4", 8), 7)),
                              6 ),
                          ACExpr (CApp (ImmId ("lam_8", 5), [ImmNum (4L, 4)], Snake, 3)),
                          2 ),
                      1 ) ) )
              [ (0, [("y_4", RegOffset (-8, RBP)); ("lam_8", RegOffset (-16, RBP))]);
                (6, [("x_12", RegOffset (24, RBP)); ("y_4", RegOffset (-8, RBP))]) ]
              16L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 16L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg RAX, Const 10L);
               IMov (RegOffset (-8, RBP), Reg RAX);
               IJmp (Label "lambda_end_6");
               ILabel "lambda_6";
               IPush (Reg RBP);
               ILineComment "fvs space: 8";
               ILineComment "local var space: 8";
               IMov (Reg RBP, Reg RSP);
               ISub (Reg RSP, Const 16L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Reg R11, RegOffset (16, RBP));
               ISub (Reg R11, HexConst 5L);
               IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: y_4");
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (24, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 1L);
               ICmp (Reg RAX, Const 0L);
               IJne (Label "?err_arith_not_num");
               IMov (Reg RAX, RegOffset (24, RBP));
               IAdd (Reg RAX, RegOffset (-8, RBP));
               IJo (Label "?err_overflow");
               IMov (Reg RSP, Reg RBP);
               IPop (Reg RBP);
               IRet;
               ILabel "lambda_end_6";
               ILineComment "Reserving 4 words";
               ICall (Label "?get_heap_end");
               ISub (Reg RAX, Const 32L);
               ICmp (Reg RAX, Reg R15);
               IJge (Label "$memcheck_6");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
               IMov (Reg RCX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
               IMov (Reg RDX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
               IMov (Reg RSI, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
               IMov (Reg RDI, Reg RAX);
               ICall (Label "?try_gc");
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10);
               IInstrComment
                 ( IMov (Reg R15, Reg RAX),
                   "assume gc success if returning here, so RAX holds the new heap_reg value" );
               ILabel "$memcheck_6";
               IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
               IMov (Reg R11, Label "lambda_6");
               IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
               IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
               ILineComment "free vars: 1";
               IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: y_4");
               IMov (RegOffset (24, R15), Reg RAX);
               IMov (Reg RAX, Reg R15);
               IAdd (Reg RAX, HexConst 5L);
               IAdd (Reg R15, Const 32L);
               IMov (RegOffset (-16, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-16, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 5L);
               IJne (Label "?err_call_not_closure");
               IMov (Reg RAX, RegOffset (-16, RBP));
               ISub (Reg RAX, HexConst 5L);
               IMov (Reg R11, RegOffset (0, RAX));
               ICmp (Reg R11, Const 2L);
               IJne (Label "?err_call_arity_err");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg R11, Const 8L);
               IPush (Reg R11);
               IPush (Sized (QWORD_PTR, RegOffset (-16, RBP)));
               ICall (RegOffset (8, RAX));
               IAdd (Reg RSP, Const 16L);
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10) ],
             [IAdd (Reg RSP, Const 16L); IPop (Reg RBP); IRet] );
         t_any "let rec"
           (compile_fun "our_code_starts_here" []
              (fvc_A
                 (ALetRec
                    ( [ ( "f_4",
                          CLambda
                            ( ["x_9"],
                              ACExpr (CApp (ImmId ("f_4", 8), [ImmId ("x_9", 7)], Snake, 6)),
                              5 ) ) ],
                      ACExpr (CApp (ImmId ("f_4", 4), [ImmNum (5L, 3)], Snake, 2)),
                      1 ) ) )
              [ (0, [("f_4", RegOffset (-8, RBP))]);
                (5, [("x_9", RegOffset (24, RBP)); ("f_4", RegOffset (-8, RBP))]) ]
              8L )
           ( [ ILabel "our_code_starts_here";
               IPush (Reg RBP);
               IMov (Reg RBP, Reg RSP);
               ILabel "our_code_starts_here_body";
               ISub (Reg RSP, Const 8L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L) ],
             [ IMov (Reg R11, Reg R15);
               IAdd (Reg R11, Const 5L);
               IMov (RegOffset (-8, RBP), Reg R11);
               IJmp (Label "lambda_end_5");
               ILabel "lambda_5";
               IPush (Reg RBP);
               ILineComment "fvs space: 8";
               ILineComment "local var space: 8";
               IMov (Reg RBP, Reg RSP);
               ISub (Reg RSP, Const 16L);
               IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
               IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
               IMov (Reg R11, RegOffset (16, RBP));
               ISub (Reg R11, HexConst 5L);
               IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: f_4");
               IMov (RegOffset (-8, RBP), Reg RAX);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 5L);
               IJne (Label "?err_call_not_closure");
               IMov (Reg RAX, RegOffset (-8, RBP));
               ISub (Reg RAX, HexConst 5L);
               IMov (Reg R11, RegOffset (0, RAX));
               ICmp (Reg R11, Const 2L);
               IJne (Label "?err_call_arity_err");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg R11, RegOffset (24, RBP));
               IPush (Reg R11);
               IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
               ICall (RegOffset (8, RAX));
               IAdd (Reg RSP, Const 16L);
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10);
               IMov (Reg RSP, Reg RBP);
               IPop (Reg RBP);
               IRet;
               ILabel "lambda_end_5";
               ILineComment "Reserving 4 words";
               ICall (Label "?get_heap_end");
               ISub (Reg RAX, Const 32L);
               ICmp (Reg RAX, Reg R15);
               IJge (Label "$memcheck_5");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
               IMov (Reg RCX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
               IMov (Reg RDX, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
               IMov (Reg RSI, Reg RAX);
               IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
               IMov (Reg RDI, Reg RAX);
               ICall (Label "?try_gc");
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10);
               IInstrComment
                 ( IMov (Reg R15, Reg RAX),
                   "assume gc success if returning here, so RAX holds the new heap_reg value" );
               ILabel "$memcheck_5";
               IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
               IMov (Reg R11, Label "lambda_5");
               IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
               IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
               ILineComment "free vars: 1";
               IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: f_4");
               IMov (RegOffset (24, R15), Reg RAX);
               IMov (Reg RAX, Reg R15);
               IAdd (Reg RAX, HexConst 5L);
               IAdd (Reg R15, Const 32L);
               IMov (Reg RAX, RegOffset (-8, RBP));
               IAnd (Reg RAX, HexConst 7L);
               ICmp (Reg RAX, Const 5L);
               IJne (Label "?err_call_not_closure");
               IMov (Reg RAX, RegOffset (-8, RBP));
               ISub (Reg RAX, HexConst 5L);
               IMov (Reg R11, RegOffset (0, RAX));
               ICmp (Reg R11, Const 2L);
               IJne (Label "?err_call_arity_err");
               IPush (Reg R10);
               IPush (Reg R12);
               IPush (Reg R13);
               IPush (Reg R14);
               IPush (Reg RBX);
               IPush (Reg RDI);
               IPush (Reg RSI);
               IPush (Reg RDX);
               IPush (Reg R8);
               IPush (Reg R9);
               IMov (Reg R11, Const 10L);
               IPush (Reg R11);
               IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
               ICall (RegOffset (8, RAX));
               IAdd (Reg RSP, Const 16L);
               IPop (Reg R9);
               IPop (Reg R8);
               IPop (Reg RDX);
               IPop (Reg RSI);
               IPop (Reg RDI);
               IPop (Reg RBX);
               IPop (Reg R14);
               IPop (Reg R13);
               IPop (Reg R12);
               IPop (Reg R10) ],
             [IAdd (Reg RSP, Const 8L); IPop (Reg RBP); IRet] ) ]

let compile_cexpr_suite =
  "compile_cexpr_suite"
  >::: [ t_asm_list "num"
           (compile_cexpr (fvc_C (CImmExpr (ImmNum (4L, 1)))) 0 [(0, [])] 0 false)
           [IMov (Reg RAX, Const 8L)];
         t_asm_list "bool_true"
           (compile_cexpr (fvc_C (CImmExpr (ImmBool (true, 1)))) 0 [(0, [])] 0 false)
           [IMov (Reg RAX, HexConst (-1L))];
         t_asm_list "bool_false"
           (compile_cexpr (fvc_C (CImmExpr (ImmBool (false, 1)))) 0 [(0, [])] 0 false)
           [IMov (Reg RAX, HexConst 9223372036854775807L)];
         t_asm_list "id"
           (compile_cexpr
              (fvc_C (CImmExpr (ImmId ("x#1", 1))))
              0
              [(0, [("x#1", RegOffset (-8, RBP))])]
              0 false )
           [IMov (Reg RAX, RegOffset (-8, RBP))];
         t_ice_error "id_not_found"
           (fun () -> compile_cexpr (fvc_C (CImmExpr (ImmId ("x#1", 1)))) 0 [(0, [])] 0 false)
           "Name \"x#1\" not found";
         t_asm_list "nil"
           (compile_cexpr (fvc_C (CImmExpr (ImmNil 1))) 0 [(0, [])] 0 false)
           [IMov (Reg RAX, HexConst 1L)];
         t_asm_list "if"
           (compile_cexpr
              (fvc_C
                 (CIf
                    ( ImmBool (true, 4),
                      ACExpr (CImmExpr (ImmNum (3L, 3))),
                      ACExpr (CImmExpr (ImmNum (6L, 2))),
                      1 ) ) )
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_1");
             ILabel "then_if_1";
             IMov (Reg RAX, Const 6L);
             IJmp (Label "done_if_1");
             ILabel "else_if_1";
             IMov (Reg RAX, Const 12L);
             ILabel "done_if_1" ];
         t_asm_list "if_with_app"
           (compile_cexpr
              (fvc_C
                 (CIf
                    ( ImmId ("funapp_1", 1),
                      ACExpr (CImmExpr (ImmNum (5L, 2))),
                      ACExpr (CImmExpr (ImmNum (10L, 3))),
                      4 ) ) )
              0
              [(0, [("funapp_1", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_4");
             ILabel "then_if_4";
             IMov (Reg RAX, Const 10L);
             IJmp (Label "done_if_4");
             ILabel "else_if_4";
             IMov (Reg RAX, Const 20L);
             ILabel "done_if_4" ];
         t_asm_list "nested_if"
           (compile_cexpr
              (fvc_C
                 (CIf
                    ( ImmBool (false, 7),
                      ACExpr (CImmExpr (ImmNum (5L, 6))),
                      ACExpr
                        (CIf
                           ( ImmBool (true, 5),
                             ACExpr (CImmExpr (ImmNum (10L, 4))),
                             ACExpr (CImmExpr (ImmNum (15L, 3))),
                             2 ) ),
                      1 ) ) )
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, HexConst 9223372036854775807L);
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_1");
             ILabel "then_if_1";
             IMov (Reg RAX, Const 10L);
             IJmp (Label "done_if_1");
             ILabel "else_if_1";
             IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_2");
             ILabel "then_if_2";
             IMov (Reg RAX, Const 20L);
             IJmp (Label "done_if_2");
             ILabel "else_if_2";
             IMov (Reg RAX, Const 30L);
             ILabel "done_if_2";
             ILabel "done_if_1" ];
         t_asm_list "is_bool"
           (compile_cexpr (fvc_C (CPrim1 (IsBool, ImmBool (true, 1), 2))) 0 [(0, [])] 0 false)
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             ISete (Reg AL);
             IShl (Reg RAX, Const 63L);
             IMov (Reg R11, HexConst 9223372036854775807L);
             IOr (Reg RAX, Reg R11) ];
         t_asm_list "is_num"
           (compile_cexpr (fvc_C (CPrim1 (IsNum, ImmNum (3L, 1), 2))) 0 [(0, [])] 0 false)
           [ IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             ISete (Reg AL);
             IShl (Reg RAX, Const 63L);
             IMov (Reg R11, HexConst 9223372036854775807L);
             IOr (Reg RAX, Reg R11) ];
         t_asm_list "is_tuple"
           (compile_cexpr
              (fvc_C (CPrim1 (IsTuple, ImmId ("tuple_3", 3), 2)))
              0
              [(0, [("tuple_3", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             ISete (Reg AL);
             IShl (Reg RAX, Const 63L);
             IMov (Reg R11, HexConst 9223372036854775807L);
             IOr (Reg RAX, Reg R11) ];
         t_asm_list "add1"
           (compile_cexpr (fvc_C (CPrim1 (Add1, ImmNum (3L, 1), 2))) 0 [(0, [])] 0 false)
           [ IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 6L);
             IAdd (Reg RAX, Const 2L);
             IJo (Label "?err_overflow") ];
         t_asm_list "sub1"
           (compile_cexpr (fvc_C (CPrim1 (Sub1, ImmNum (3L, 1), 2))) 0 [(0, [])] 0 false)
           [ IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 6L);
             ISub (Reg RAX, Const 2L);
             IJo (Label "?err_overflow") ];
         t_asm_list "not"
           (compile_cexpr (fvc_C (CPrim1 (Not, ImmBool (true, 1), 2))) 0 [(0, [])] 0 false)
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_logic_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst (-9223372036854775808L));
             IXor (Reg RAX, Reg R11) ];
         t_asm_list "print"
           (compile_cexpr
              (fvc_C (CApp (ImmId ("print", 3), [ImmNum (4L, 2)], Native, 1)))
              0
              [(0, [])]
              0 false )
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 8L);
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?print");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "print_stack"
           (compile_cexpr (fvc_C (CPrim1 (PrintStack, ImmNum (3L, 1), 2))) 0 [(0, [])] 0 false)
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 6L);
             IMov (Reg RDI, Reg RAX);
             IMov (Reg RSI, Reg RBP);
             IMov (Reg RDX, Reg RSP);
             IMov (Reg RCX, Const 0L);
             ICall (Label "?print_stack");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "plus"
           (compile_cexpr
              (fvc_C (CPrim2 (Plus, ImmNum (3L, 1), ImmNum (4L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 6L);
             IAdd (Reg RAX, Const 8L);
             IJo (Label "?err_overflow") ];
         t_asm_list "minus"
           (compile_cexpr
              (fvc_C (CPrim2 (Minus, ImmNum (4L, 1), ImmNum (3L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             ISub (Reg RAX, Const 6L);
             IJo (Label "?err_overflow") ];
         t_asm_list "times"
           (compile_cexpr
              (fvc_C (CPrim2 (Times, ImmNum (5L, 1), ImmNum (8L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 10L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 16L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 10L);
             ISar (Reg RAX, Const 1L);
             IMul (Reg RAX, Const 16L);
             IJo (Label "?err_overflow") ];
         t_ice_error "and_ice_error"
           (fun () ->
             compile_cexpr
               (fvc_C (CPrim2 (And, ImmBool (false, 1), ImmBool (true, 2), 3)))
               0
               [(0, [])]
               0 false )
           "Impossible: non-desugared primitive operation";
         t_ice_error "ir_ice_error"
           (fun () ->
             compile_cexpr
               (fvc_C (CPrim2 (Or, ImmBool (false, 1), ImmBool (true, 2), 3)))
               0
               [(0, [])]
               0 false )
           "Impossible: non-desugared primitive operation";
         t_asm_list "greater"
           (compile_cexpr
              (fvc_C (CPrim2 (Greater, ImmNum (10L, 1), ImmNum (9L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 20L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 18L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 20L);
             IMov (Reg R11, Const 18L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJg (Label "done_greater_3");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             ILabel "done_greater_3" ];
         t_asm_list "greatereq"
           (compile_cexpr
              (fvc_C (CPrim2 (GreaterEq, ImmNum (10L, 1), ImmNum (9L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 20L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 18L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 20L);
             IMov (Reg R11, Const 18L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJge (Label "done_greatereq_3");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             ILabel "done_greatereq_3" ];
         t_asm_list "less"
           (compile_cexpr
              (fvc_C (CPrim2 (Less, ImmNum (10L, 1), ImmNum (9L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 20L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 18L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 20L);
             IMov (Reg R11, Const 18L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJl (Label "done_less_3");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             ILabel "done_less_3" ];
         t_asm_list "lesseq"
           (compile_cexpr
              (fvc_C (CPrim2 (LessEq, ImmNum (10L, 1), ImmNum (9L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, Const 20L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 18L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_comp_not_num");
             IMov (Reg RAX, Const 20L);
             IMov (Reg R11, Const 18L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJle (Label "done_lesseq_3");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             ILabel "done_lesseq_3" ];
         t_asm_list "eq"
           (compile_cexpr
              (fvc_C (CPrim2 (Eq, ImmBool (false, 1), ImmNum (9L, 2), 3)))
              0
              [(0, [])]
              0 false )
           [ IMov (Reg RAX, HexConst 9223372036854775807L);
             IMov (Reg R11, Const 18L);
             ICmp (Reg RAX, Reg R11);
             IMov (Reg RAX, HexConst (-1L));
             IJe (Label "done_eq_3");
             IMov (Reg RAX, HexConst 9223372036854775807L);
             ILabel "done_eq_3" ];
         t_asm_list "check_size"
           (compile_cexpr
              (fvc_C (CPrim2 (CheckSize, ImmId ("tup?1_4", 16), ImmNum (2L, 15), 14)))
              0
              [(0, [("tup?1_4", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_tuple_bad_destruct");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_tuple_bad_destruct");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 4L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJne (Label "?err_tuple_bad_destruct") ];
         t_asm_list "non_rec_fun_app"
           (compile_cexpr
              (fvc_C (CApp (ImmId ("f", 0), [ImmNum (5L, 2)], Snake, 1)))
              0
              [(0, [("f", RegOffset (-8, RBP))])]
              1 false )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "non_rec_fun_app_multiple_args"
           (compile_cexpr
              (fvc_C (CApp (ImmId ("f", 0), [ImmNum (5L, 2); ImmNum (2L, 3)], Snake, 1)))
              0
              [(0, [("f", RegOffset (-8, RBP))])]
              2 false )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 4L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 4L);
             IPush (Reg R11);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 24L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "tuple_creation"
           (compile_cexpr
              (fvc_C (CTuple ([ImmNum (1L, 2); ImmNum (2L, 3); ImmNum (3L, 4)], 1)))
              0
              [(0, [])]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_1");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_1";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 2L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "tuple_get"
           (compile_cexpr
              (fvc_C (CGetItem (ImmId ("tuple_4", 4), ImmNum (0L, 3), 2)))
              0
              [(0, [("tuple_4", RegOffset (-8, RBP))])]
              0 true )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_get_not_tuple");
             IMov (Reg RAX, Const 0L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_get_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 0L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_get_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_get_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX)) ];
         t_asm_list "tuple_set"
           (compile_cexpr
              (fvc_C (CSetItem (ImmId ("tuple_4", 5), ImmNum (0L, 4), ImmNum (2L, 3), 2)))
              0
              [(0, [("tuple_4", RegOffset (-8, RBP))])]
              0 true )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_set_not_tuple");
             IMov (Reg RAX, Const 0L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_set_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 0L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_set_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_set_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (RegOffset (0, RAX), Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX)) ];
         t_asm_list "tuple_creation_ids"
           (compile_cexpr
              (fvc_C (CTuple ([ImmId ("x_4", 4); ImmId ("y_7", 5)], 3)))
              0
              [(0, [("x_4", RegOffset (-8, RBP)); ("y_7", RegOffset (-16, RBP))])]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_3");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_3";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 4L);
             IMov (Reg R11, RegOffset (-8, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, RegOffset (-16, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "input"
           (compile_cexpr (fvc_C (CApp (ImmId ("input", 0), [], Native, 1))) 0 [(0, [])] 0 true)
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             ICall (Label "?input");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "native_calls_2_args"
           (compile_cexpr
              (fvc_C (CApp (ImmId ("print", 0), [ImmNum (1L, 2)], Native, 1)))
              0
              [(0, [])]
              0 true )
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 2L);
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?print");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "native_calls_with_more_than_7_args"
           (compile_cexpr
              (fvc_C
                 (CApp
                    ( ImmId ("testarg", 0),
                      [ ImmNum (1L, 2);
                        ImmNum (2L, 3);
                        ImmNum (3L, 4);
                        ImmNum (4L, 5);
                        ImmNum (5L, 6);
                        ImmNum (6L, 7);
                        ImmNum (7L, 8);
                        ImmNum (8L, 9);
                        ImmNum (9L, 10) ],
                      Native,
                      1 ) ) )
              0
              [(0, [])]
              0 true )
           [ IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Const 18L);
             IPush (Reg RAX);
             IMov (Reg RAX, Const 16L);
             IPush (Reg RAX);
             IMov (Reg RAX, Const 14L);
             IPush (Reg RAX);
             IMov (Reg RAX, Const 12L);
             IMov (Reg R9, Reg RAX);
             IMov (Reg RAX, Const 10L);
             IMov (Reg R8, Reg RAX);
             IMov (Reg RAX, Const 8L);
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Const 6L);
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Const 4L);
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Const 2L);
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?testarg");
             IAdd (Reg RSP, Const 24L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "snake_fun_call_tuple"
           (compile_cexpr
              (fvc_C (CApp (ImmId ("f", 0), [ImmId ("t1_4", 4); ImmId ("t2_10", 5)], Snake, 3)))
              0
              [ ( 0,
                  [ ("f", RegOffset (-8, RBP));
                    ("t1_4", RegOffset (-16, RBP));
                    ("t2_10", RegOffset (-24, RBP)) ] ) ]
              0 true )
           [ IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 4L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, RegOffset (-24, RBP));
             IPush (Reg R11);
             IMov (Reg R11, RegOffset (-16, RBP));
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 24L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "lambda_lit_zero_args"
           (compile_cexpr
              (fvc_C (CLambda ([], ACExpr (CImmExpr (ImmNum (100L, 1))), 2)))
              0
              [(0, []); (2, [])]
              0 false )
           [ IJmp (Label "lambda_end_2");
             ILabel "lambda_2";
             IPush (Reg RBP);
             ILineComment "fvs space: 0";
             ILineComment "local var space: 0";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 0L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IMov (Reg RAX, Const 200L);
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_2";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_2");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_2";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 0L);
             IMov (Reg R11, Label "lambda_2");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L);
             ILineComment "free vars: 0";
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "lambda_lit_one_arg"
           (compile_cexpr
              (fvc_C (CLambda (["x_4"], ACExpr (CImmExpr (ImmId ("x_4", 2))), 1)))
              0
              [(0, []); (1, [("x_4", RegOffset (24, RBP))])]
              0 false )
           [ IJmp (Label "lambda_end_1");
             ILabel "lambda_1";
             IPush (Reg RBP);
             ILineComment "fvs space: 0";
             ILineComment "local var space: 0";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 0L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IMov (Reg RAX, RegOffset (24, RBP));
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_1";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_1");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_1";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_1");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L);
             ILineComment "free vars: 0";
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "lambda_freevars"
           (compile_cexpr
              (fvc_C
                 (CLambda
                    ( ["y_8"],
                      ALet
                        ( "binop_4",
                          CPrim2 (Plus, ImmId ("x", 8), ImmId ("y_8", 7), 6),
                          ACExpr (CPrim2 (Plus, ImmId ("binop_4", 5), ImmId ("z", 4), 3)),
                          2 ),
                      1 ) ) )
              1
              [ (0, []);
                ( 1,
                  [ ("y_8", RegOffset (24, RBP));
                    ("binop_4", RegOffset (-24, RBP));
                    ("x", RegOffset (8, RBP));
                    ("z", RegOffset (16, RBP)) ] ) ]
              0 false )
           [ IJmp (Label "lambda_end_1");
             ILabel "lambda_1";
             IPush (Reg RBP);
             ILineComment "fvs space: 16";
             ILineComment "local var space: 24";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 40L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (24, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (32, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: z");
             IMov (RegOffset (16, RBP), Reg RAX);
             IInstrComment (IMov (Reg RAX, RegOffset (32, R11)), "load fv: x");
             IMov (RegOffset (8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (24, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (8, RBP));
             IAdd (Reg RAX, RegOffset (24, RBP));
             IJo (Label "?err_overflow");
             IMov (RegOffset (-24, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-24, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (16, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-24, RBP));
             IAdd (Reg RAX, RegOffset (16, RBP));
             IJo (Label "?err_overflow");
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_1";
             ILineComment "Reserving 6 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 48L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_1");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 48L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_1";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_1");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 4L);
             ILineComment "free vars: 2";
             IInstrComment (IMov (Reg RAX, RegOffset (16, RBP)), "pack fv: z");
             IMov (RegOffset (24, R15), Reg RAX);
             IInstrComment (IMov (Reg RAX, RegOffset (8, RBP)), "pack fv: x");
             IMov (RegOffset (32, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 48L) ] ]

let compile_aexpr_suite =
  "compile_aexpr_suite"
  >::: [ t_asm_list "let_x"
           (compile_aexpr
              (fvc_A
                 (ALet ("x#3", CImmExpr (ImmNum (3L, 3)), ACExpr (CImmExpr (ImmId ("x#3", 2))), 1)) )
              0
              [(0, [("x#3", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, Const 6L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP)) ];
         t_asm_list "let_in_let"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x#8",
                      CImmExpr (ImmNum (3L, 7)),
                      ALet
                        ( "y#6",
                          CImmExpr (ImmNum (4L, 6)),
                          ACExpr (CPrim2 (Plus, ImmId ("x#8", 5), ImmNum (4L, 4), 3)),
                          2 ),
                      1 ) ) )
              0
              [(0, [("x#8", RegOffset (-8, RBP)); ("y#6", RegOffset (-16, RBP))])]
              0 false )
           [ IMov (Reg RAX, Const 6L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, Const 8L);
             IMov (RegOffset (-16, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAdd (Reg RAX, Const 8L);
             IJo (Label "?err_overflow") ];
         t_asm_list "let_y_gets_x"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x#3",
                      CImmExpr (ImmNum (2L, 7)),
                      ALet
                        ( "y#5",
                          CPrim2 (Plus, ImmId ("x#3", 6), ImmNum (1L, 5), 4),
                          ACExpr (CImmExpr (ImmId ("y#5", 3))),
                          2 ),
                      1 ) ) )
              0
              [(0, [("x#3", RegOffset (-8, RBP)); ("y#5", RegOffset (-16, RBP))])]
              0 false )
           [ IMov (Reg RAX, Const 4L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 2L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAdd (Reg RAX, Const 2L);
             IJo (Label "?err_overflow");
             IMov (RegOffset (-16, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-16, RBP)) ];
         t_asm_list "let_x_shadow"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x#8",
                      CImmExpr (ImmNum (5L, 7)),
                      ALet
                        ( "x#4",
                          CPrim2 (Plus, ImmId ("x#8", 6), ImmNum (6L, 5), 4),
                          ACExpr (CImmExpr (ImmId ("x#4", 3))),
                          2 ),
                      1 ) ) )
              0
              [(0, [("x#8", RegOffset (-8, RBP)); ("x#4", RegOffset (-16, RBP))])]
              0 false )
           [ IMov (Reg RAX, Const 10L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 12L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAdd (Reg RAX, Const 12L);
             IJo (Label "?err_overflow");
             IMov (RegOffset (-16, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-16, RBP)) ];
         t_asm_list "if_in_let"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x#6",
                      CImmExpr (ImmBool (true, 6)),
                      ACExpr
                        (CIf
                           ( ImmBool (true, 5),
                             ACExpr (CImmExpr (ImmNum (5L, 4))),
                             ACExpr (CImmExpr (ImmNum (10L, 3))),
                             2 ) ),
                      1 ) ) )
              0
              [(0, [("x#6", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, HexConst (-1L));
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_2");
             ILabel "then_if_2";
             IMov (Reg RAX, Const 10L);
             IJmp (Label "done_if_2");
             ILabel "else_if_2";
             IMov (Reg RAX, Const 20L);
             ILabel "done_if_2" ];
         t_asm_list "if_in_let_bindings"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x#3",
                      CIf
                        ( ImmBool (true, 6),
                          ACExpr (CImmExpr (ImmNum (10L, 5))),
                          ACExpr (CImmExpr (ImmNum (15L, 4))),
                          3 ),
                      ACExpr (CImmExpr (ImmId ("x#3", 2))),
                      1 ) ) )
              0
              [(0, [("x#3", RegOffset (-8, RBP))])]
              0 false )
           [ IMov (Reg RAX, HexConst (-1L));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 7L);
             IJne (Label "?err_if_not_bool");
             IMov (Reg RAX, HexConst (-1L));
             IMov (Reg R11, HexConst (-1L));
             ICmp (Reg RAX, Reg R11);
             IJne (Label "else_if_3");
             ILabel "then_if_3";
             IMov (Reg RAX, Const 20L);
             IJmp (Label "done_if_3");
             ILabel "else_if_3";
             IMov (Reg RAX, Const 30L);
             ILabel "done_if_3";
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP)) ];
         t_asm_list "let tuple creation"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x_4",
                      CImmExpr (ImmNum (5L, 7)),
                      ALet
                        ( "y_7",
                          CImmExpr (ImmNum (3L, 6)),
                          ACExpr (CTuple ([ImmId ("x_4", 4); ImmId ("y_7", 5)], 3)),
                          2 ),
                      1 ) ) )
              0
              [(0, [("x_4", RegOffset (-8, RBP)); ("y_7", RegOffset (-16, RBP))])]
              0 true )
           [ IMov (Reg RAX, Const 10L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, Const 6L);
             IMov (RegOffset (-16, RBP), Reg RAX);
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_3");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_3";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 4L);
             IMov (Reg R11, RegOffset (-8, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, RegOffset (-16, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "let tup binding creation"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "x_4",
                      CTuple ([ImmNum (1L, 11); ImmNum (2L, 12); ImmNum (3L, 13)], 10),
                      ALet
                        ( "y_10",
                          CTuple ([ImmNum (2L, 7); ImmNum (3L, 8); ImmNum (4L, 9)], 6),
                          ACExpr (CTuple ([ImmId ("x_4", 4); ImmId ("y_10", 5)], 3)),
                          2 ),
                      1 ) ) )
              0
              [(0, [("x_4", RegOffset (-8, RBP)); ("y_10", RegOffset (-16, RBP))])]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_10");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_10";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 2L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_6");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_6";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 4L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 8L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-16, RBP), Reg RAX);
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_3");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_3";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 4L);
             IMov (Reg R11, RegOffset (-8, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, RegOffset (-16, RBP));
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "tuple access"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "tuple_4",
                      CTuple ([ImmNum (1L, 6); ImmNum (2L, 7); ImmNum (3L, 8)], 5),
                      ACExpr (CGetItem (ImmId ("tuple_4", 4), ImmNum (1L, 3), 2)),
                      1 ) ) )
              0
              [(0, [("tuple_4", RegOffset (-8, RBP))])]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_5");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_5";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 2L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_get_not_tuple");
             IMov (Reg RAX, Const 2L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_get_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 2L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_get_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_get_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX)) ];
         t_asm_list "tuple setting"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "t_4",
                      CTuple ([ImmNum (1L, 7); ImmNum (2L, 8); ImmNum (3L, 9)], 6),
                      ACExpr (CSetItem (ImmId ("t_4", 5), ImmNum (1L, 4), ImmNum (4L, 3), 2)),
                      1 ) ) )
              0
              [(0, [("t_4", RegOffset (-8, RBP))])]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_6");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_6";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 2L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_set_not_tuple");
             IMov (Reg RAX, Const 2L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_set_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 2L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_set_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_set_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg R11, Const 8L);
             IMov (RegOffset (0, RAX), Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX)) ];
         t_asm_list "tup chain of sets"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "three_4",
                      CTuple ([ImmNum (0L, 17); ImmNum (0L, 18); ImmNum (0L, 19)], 16),
                      ALet
                        ( "three1_11",
                          CSetItem (ImmId ("three_4", 15), ImmNum (0L, 14), ImmNum (1L, 13), 12),
                          ALet
                            ( "three2_18",
                              CSetItem (ImmId ("three_4", 11), ImmNum (1L, 10), ImmNum (2L, 9), 8),
                              ACExpr
                                (CSetItem (ImmId ("three_4", 7), ImmNum (3L, 6), ImmNum (3L, 5), 4)),
                              3 ),
                          2 ),
                      1 ) ) )
              0
              [ ( 0,
                  [ ("three_4", RegOffset (-8, RBP));
                    ("three1_11", RegOffset (-16, RBP));
                    ("three2_18", RegOffset (-24, RBP)) ] ) ]
              0 true )
           [ ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_16");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_16";
             IMov (Reg RAX, Reg R15);
             IOr (Reg RAX, Const 1L);
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 6L);
             IMov (Reg R11, Const 0L);
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Reg R11, Const 0L);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Reg R11);
             IMov (Reg R11, Const 0L);
             IMov (Sized (QWORD_PTR, RegOffset (24, R15)), Reg R11);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_set_not_tuple");
             IMov (Reg RAX, Const 0L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_set_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 0L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_set_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_set_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg R11, Const 2L);
             IMov (RegOffset (0, RAX), Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX));
             IMov (RegOffset (-16, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_set_not_tuple");
             IMov (Reg RAX, Const 2L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_set_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 2L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_set_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_set_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg R11, Const 4L);
             IMov (RegOffset (0, RAX), Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX));
             IMov (RegOffset (-24, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             ICmp (Reg RAX, HexConst 1L);
             IJz (Label "?err_nil_deref");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 1L);
             IJne (Label "?err_set_not_tuple");
             IMov (Reg RAX, Const 6L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_set_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, Const 1L);
             IMov (Reg R11, Const 6L);
             IAdd (Reg R11, Const 2L);
             ICmp (Reg R11, RegOffset (0, RAX));
             IJg (Label "?err_set_high_index");
             ICmp (Reg R11, Const 2L);
             IJl (Label "?err_set_low_index");
             ISub (Reg R11, Const 2L);
             ISar (Reg R11, Const 1L);
             IAdd (Reg R11, Const 1L);
             IShl (Reg R11, Const 3L);
             IAdd (Reg RAX, Reg R11);
             IMov (Reg R11, Const 6L);
             IMov (RegOffset (0, RAX), Reg R11);
             IMov (Reg RAX, RegOffset (0, RAX)) ];
         t_asm_list "lambda"
           (compile_aexpr
              (fvc_A (ACExpr (CLambda (["x_4"], ACExpr (CImmExpr (ImmId ("x_4", 2))), 1))))
              0
              [(0, []); (1, [("x_4", RegOffset (24, RBP))])]
              0 false )
           [ IJmp (Label "lambda_end_1");
             ILabel "lambda_1";
             IPush (Reg RBP);
             ILineComment "fvs space: 0";
             ILineComment "local var space: 0";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 0L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IMov (Reg RAX, RegOffset (24, RBP));
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_1";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_1");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_1";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_1");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L);
             ILineComment "free vars: 0";
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "lambda fv"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "y_4",
                      CImmExpr (ImmNum (5L, 6)),
                      ACExpr
                        (CLambda
                           ( ["x_10"],
                             ACExpr (CPrim2 (Plus, ImmId ("x_10", 5), ImmId ("y_4", 4), 3)),
                             2 ) ),
                      1 ) ) )
              0
              [ (0, [("y_4", RegOffset (-8, RBP))]);
                (2, [("x_10", RegOffset (24, RBP)); ("y_4", RegOffset (-8, RBP))]) ]
              0 false )
           [ IMov (Reg RAX, Const 10L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IJmp (Label "lambda_end_2");
             ILabel "lambda_2";
             IPush (Reg RBP);
             ILineComment "fvs space: 8";
             ILineComment "local var space: 8";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 16L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: y_4");
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (24, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (24, RBP));
             IAdd (Reg RAX, RegOffset (-8, RBP));
             IJo (Label "?err_overflow");
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_2";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_2");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_2";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_2");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
             ILineComment "free vars: 1";
             IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: y_4");
             IMov (RegOffset (24, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "lambda fvs with let"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "y_4",
                      CImmExpr (ImmNum (5L, 10)),
                      ACExpr
                        (CLambda
                           ( ["x_16"],
                             ALet
                               ( "k_9",
                                 CPrim2 (Plus, ImmId ("x_16", 9), ImmNum (4L, 8), 7),
                                 ACExpr (CPrim2 (Plus, ImmId ("k_9", 6), ImmId ("y_4", 5), 4)),
                                 3 ),
                             2 ) ),
                      1 ) ) )
              0
              [ (0, [("y_4", RegOffset (-8, RBP))]);
                ( 2,
                  [ ("k_9", RegOffset (-16, RBP));
                    ("x_16", RegOffset (24, RBP));
                    ("y_4", RegOffset (-8, RBP)) ] ) ]
              0 false )
           [ IMov (Reg RAX, Const 10L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IJmp (Label "lambda_end_2");
             ILabel "lambda_2";
             IPush (Reg RBP);
             ILineComment "fvs space: 8";
             ILineComment "local var space: 16";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 24L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (16, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: y_4");
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (24, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (24, RBP));
             IAdd (Reg RAX, Const 8L);
             IJo (Label "?err_overflow");
             IMov (RegOffset (-16, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-16, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (-16, RBP));
             IAdd (Reg RAX, RegOffset (-8, RBP));
             IJo (Label "?err_overflow");
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_2";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_2");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_2";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_2");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
             ILineComment "free vars: 1";
             IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: y_4");
             IMov (RegOffset (24, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L) ];
         t_asm_list "lambda apply"
           (compile_aexpr
              (fvc_A
                 (ALet
                    ( "f_4",
                      CLambda
                        (["x_9"], ACExpr (CPrim2 (Plus, ImmId ("x_9", 8), ImmNum (4L, 7), 6)), 5),
                      ACExpr (CApp (ImmId ("f_4", 4), [ImmNum (5L, 3)], Snake, 2)),
                      1 ) ) )
              0
              [(0, [("f_4", RegOffset (-8, RBP))]); (5, [("x_9", RegOffset (24, RBP))])]
              0 false )
           [ IJmp (Label "lambda_end_5");
             ILabel "lambda_5";
             IPush (Reg RBP);
             ILineComment "fvs space: 0";
             ILineComment "local var space: 0";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 0L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IMov (Reg RAX, RegOffset (24, RBP));
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, Const 8L);
             IAnd (Reg RAX, HexConst 1L);
             ICmp (Reg RAX, Const 0L);
             IJne (Label "?err_arith_not_num");
             IMov (Reg RAX, RegOffset (24, RBP));
             IAdd (Reg RAX, Const 8L);
             IJo (Label "?err_overflow");
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_5";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_5");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_5";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_5");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 0L);
             ILineComment "free vars: 0";
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L);
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 10L);
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "let rec inf rec"
           (compile_aexpr
              (fvc_A
                 (ALetRec
                    ( [ ( "f_4",
                          CLambda
                            ( ["x_9"],
                              ACExpr (CApp (ImmId ("f_4", 8), [ImmId ("x_9", 7)], Snake, 6)),
                              5 ) ) ],
                      ACExpr (CApp (ImmId ("f_4", 4), [ImmNum (1L, 3)], Snake, 2)),
                      1 ) ) )
              0
              [ (0, [("f_4", RegOffset (-8, RBP))]);
                (5, [("x_9", RegOffset (24, RBP)); ("f_4", RegOffset (-8, RBP))]) ]
              0 false )
           [ IMov (Reg R11, Reg R15);
             IAdd (Reg R11, Const 5L);
             IMov (RegOffset (-8, RBP), Reg R11);
             IJmp (Label "lambda_end_5");
             ILabel "lambda_5";
             IPush (Reg RBP);
             ILineComment "fvs space: 8";
             ILineComment "local var space: 8";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 16L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: f_4");
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, RegOffset (24, RBP));
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_5";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_5");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_5";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_5");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
             ILineComment "free vars: 1";
             IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: f_4");
             IMov (RegOffset (24, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 2L);
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ];
         t_asm_list "let rec mutual rec"
           (compile_aexpr
              (fvc_A
                 (ALetRec
                    ( [ ( "f_4",
                          CLambda
                            ( ["x_9"],
                              ACExpr (CApp (ImmId ("g_11", 8), [ImmId ("x_9", 7)], Snake, 6)),
                              5 ) );
                        ( "g_11",
                          CLambda
                            ( ["x_16"],
                              ACExpr (CApp (ImmId ("f_4", 12), [ImmId ("x_16", 11)], Snake, 10)),
                              9 ) ) ],
                      ACExpr (CApp (ImmId ("f_4", 4), [ImmNum (1L, 3)], Snake, 2)),
                      1 ) ) )
              0
              [ (0, [("g_11", RegOffset (-16, RBP)); ("f_4", RegOffset (-8, RBP))]);
                (5, [("x_9", RegOffset (24, RBP)); ("g_11", RegOffset (-8, RBP))]);
                (9, [("x_16", RegOffset (24, RBP)); ("f_4", RegOffset (-8, RBP))]) ]
              0 false )
           [ IMov (Reg R11, Reg R15);
             IAdd (Reg R11, Const 5L);
             IMov (RegOffset (-8, RBP), Reg R11);
             IMov (Reg R11, Reg R15);
             IAdd (Reg R11, Const 37L);
             IMov (RegOffset (-16, RBP), Reg R11);
             IJmp (Label "lambda_end_5");
             ILabel "lambda_5";
             IPush (Reg RBP);
             ILineComment "fvs space: 8";
             ILineComment "local var space: 8";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 16L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: g_11");
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, RegOffset (24, RBP));
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_5";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_5");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_5";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_5");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
             ILineComment "free vars: 1";
             IInstrComment (IMov (Reg RAX, RegOffset (-16, RBP)), "pack fv: g_11");
             IMov (RegOffset (24, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L);
             IJmp (Label "lambda_end_9");
             ILabel "lambda_9";
             IPush (Reg RBP);
             ILineComment "fvs space: 8";
             ILineComment "local var space: 8";
             IMov (Reg RBP, Reg RSP);
             ISub (Reg RSP, Const 16L);
             IMov (Sized (QWORD_PTR, RegOffset (0, RSP)), HexConst 51217366750L);
             IMov (Sized (QWORD_PTR, RegOffset (8, RSP)), HexConst 51217366750L);
             IMov (Reg R11, RegOffset (16, RBP));
             ISub (Reg R11, HexConst 5L);
             IInstrComment (IMov (Reg RAX, RegOffset (24, R11)), "load fv: f_4");
             IMov (RegOffset (-8, RBP), Reg RAX);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, RegOffset (24, RBP));
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IMov (Reg RSP, Reg RBP);
             IPop (Reg RBP);
             IRet;
             ILabel "lambda_end_9";
             ILineComment "Reserving 4 words";
             ICall (Label "?get_heap_end");
             ISub (Reg RAX, Const 32L);
             ICmp (Reg RAX, Reg R15);
             IJge (Label "$memcheck_9");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RSP));
             IMov (Reg RCX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg RBP));
             IMov (Reg RDX, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Const 32L));
             IMov (Reg RSI, Reg RAX);
             IMov (Reg RAX, Sized (QWORD_PTR, Reg R15));
             IMov (Reg RDI, Reg RAX);
             ICall (Label "?try_gc");
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10);
             IInstrComment
               ( IMov (Reg R15, Reg RAX),
                 "assume gc success if returning here, so RAX holds the new heap_reg value" );
             ILabel "$memcheck_9";
             IMov (Sized (QWORD_PTR, RegOffset (0, R15)), Const 2L);
             IMov (Reg R11, Label "lambda_9");
             IMov (Sized (QWORD_PTR, RegOffset (8, R15)), Reg R11);
             IMov (Sized (QWORD_PTR, RegOffset (16, R15)), Const 2L);
             ILineComment "free vars: 1";
             IInstrComment (IMov (Reg RAX, RegOffset (-8, RBP)), "pack fv: f_4");
             IMov (RegOffset (24, R15), Reg RAX);
             IMov (Reg RAX, Reg R15);
             IAdd (Reg RAX, HexConst 5L);
             IAdd (Reg R15, Const 32L);
             IMov (Reg RAX, RegOffset (-8, RBP));
             IAnd (Reg RAX, HexConst 7L);
             ICmp (Reg RAX, Const 5L);
             IJne (Label "?err_call_not_closure");
             IMov (Reg RAX, RegOffset (-8, RBP));
             ISub (Reg RAX, HexConst 5L);
             IMov (Reg R11, RegOffset (0, RAX));
             ICmp (Reg R11, Const 2L);
             IJne (Label "?err_call_arity_err");
             IPush (Reg R10);
             IPush (Reg R12);
             IPush (Reg R13);
             IPush (Reg R14);
             IPush (Reg RBX);
             IPush (Reg RDI);
             IPush (Reg RSI);
             IPush (Reg RDX);
             IPush (Reg R8);
             IPush (Reg R9);
             IMov (Reg R11, Const 2L);
             IPush (Reg R11);
             IPush (Sized (QWORD_PTR, RegOffset (-8, RBP)));
             ICall (RegOffset (8, RAX));
             IAdd (Reg RSP, Const 16L);
             IPop (Reg R9);
             IPop (Reg R8);
             IPop (Reg RDX);
             IPop (Reg RSI);
             IPop (Reg RDI);
             IPop (Reg RBX);
             IPop (Reg R14);
             IPop (Reg R13);
             IPop (Reg R12);
             IPop (Reg R10) ] ]

let compile_run_suite =
  "compile_run_suite"
  >::: [ t "plain_4" "4" "" "4";
         t "plain_true" "true" "" "true";
         t "plain_false" "false" "" "false";
         t "comment" "# hello, i am a comment\n5" "" "5";
         t "let_40" "let x = 40 in x" "" "40";
         t "let_false" "let x = false in x" "" "false";
         t "let_true" "let x = true in x" "" "true";
         t "let_x_in_x" "let x = 5 in x" "" "5";
         t "let_x_in_x_plus" "let x = 5 in x + 5" "" "10";
         t "let_x_in_x_plus_x" "let x = 7 in x + x" "" "14";
         t "let_x_y_plus" "let x = 3, y = 4 in x * y" "" "12";
         t "let_in_let" "let x = 4, y = 2 in let z = 4 in x + y + z" "" "10";
         t "let_in_let_minus" "let x = 5, y = 3 in let z = 9 in x - y - z" "" "-7";
         t "let_in_let_times" "let x = 4, y = 2 in let z = 4 in x * y * z" "" "32";
         t "let_op_in_bindings" "let f = 30 in let x = 10, y = (f + 5) in y" "" "35";
         t "let_in_let_bindings" "let x = (let y = 3 + 3 in y) in x + 2" "" "8";
         t "let_in_let_bindings_shadow" "let x = (let x = 10 in x) in x" "" "10";
         t "let_shadow" "let x = 3 in let x = 4 in x" "" "4";
         t "let_bindings_prev_binding" "let x = 10, y = x in y" "" "10";
         t "let_bindings_prev_binding_add1" "let x = 10, y = add1(x) in y" "" "11";
         t "let_bindings_prev_binding_op" "let x = 10, y = (x + 5) in y" "" "15";
         t "let_plus_let" "(let x = 1 in x) + (let x = 2 in x)" "" "3";
         t "let_times_let_in_binding"
           "let x = ((let y = 2 + 2 in y) * (let z = 2 - 6 in z)) in x + 10" "" "-6";
         t "let_times_let_in_binding_prim1"
           "let x = (sub1(let y = 2 + 2 in y) * (let z = 2 - 6 in z)) in x + 10" "" "-2";
         t "is_bool_true" "isbool(true)" "" "true";
         t "is_bool_false" "isbool(false)" "" "true";
         t "is_bool_num_even" "isbool(10)" "" "false";
         t "is_bool_num_odd" "isbool(11)" "" "false";
         t "is_bool_15" "isbool(15)" "" "false";
         t "is_num_true" "isnum(true)" "" "false";
         t "is_num_false" "isnum(false)" "" "false";
         t "is_num_num_even" "isnum(10)" "" "true";
         t "is_num_num_odd" "isnum(11)" "" "true";
         t "isbool_isnum" "isbool(isnum(6))" "" "true";
         t "isnum_isbool" "isnum(isbool(false))" "" "false";
         t "add1_num_even" "add1(6)" "" "7";
         t "add1_num_odd" "add1(5)" "" "6";
         t "add1_num_neg" "add1(-5)" "" "-4";
         t "add1_let" "let x = 5 in add1(x)" "" "6";
         t "add1_let_in_binding" "let x = add1(5) in x" "" "6";
         te "add1_bool_true" "add1(true)" "" "arithmetic expected a number";
         te "add1_bool_false" "add1(false)" "" "arithmetic expected a number";
         te "add1_bool_let" "let x = false in add1(x)" "" "arithmetic expected a number";
         te "add1_overflow" "add1(4611686018427387903)" "" "overflow";
         t "sub1_num_even" "sub1(6)" "" "5";
         t "sub1_num_odd" "sub1(5)" "" "4";
         t "sub1_num_neg" "sub1(-5)" "" "-6";
         t "sub1_let" "let x = 5 in sub1(x)" "" "4";
         t "sub1_let_in_binding" "let x = sub1(5) in x" "" "4";
         te "sub1_bool_true" "sub1(true)" "" "arithmetic expected a number";
         te "sub1_bool_false" "sub1(false)" "" "arithmetic expected a number";
         te "sub1_bool_let" "let x = false in sub1(x)" "" "arithmetic expected a number";
         te "sub1_overflow" "sub1(-4611686018427387904)" "" "overflow";
         t "not_false" "!(false)" "" "true";
         t "not_true" "!(true)" "" "false";
         t "not_not_true" "!(!(true))" "" "true";
         t "not_not_false" "!(!(false))" "" "false";
         te "not_num" "!(5)" "" "logic expected a boolean";
         t "print_num" "print(5)" "" "5\n5";
         t "print_bool" "print(true)" "" "true\ntrue";
         t "print_inside" "isnum(print(5))" "" "5\ntrue";
         t "print_in_let_binding" "let x = print(5) in x" "" "5\n5";
         t "print_in_let" "let x = 5 in print(5)" "" "5\n5";
         t "print_in_let_multiple_bindings" "let x = print(3), y = print(6) in y" "" "3\n6\n6";
         t "print_in_print" "print(print(3))" "" "3\n3\n3";
         t "print_in_let_nested" "let x = print(let x = print(30) + 10 in x) in print(x + 10) + 10"
           "" "30\n40\n50\n60";
         t "print_given_ex" "let x = 1 in\nlet y = print(x + 1) in\nprint(y + 2)" "" "2\n4\n4";
         t "print_plus" "print(print(1) + print(2))" "" "1\n2\n3\n3";
         t "plus_2_3" "2 + 3" "" "5";
         t "minus_6_2" "6 - 2" "" "4";
         t "minus_3_8" "3 - 8" "" "-5";
         t "times_3_4" "3 * 4" "" "12";
         t "minus_neg_lit" "3 - -10" "" "13";
         t "plus_nest" "(1 + 2) + (3 + 4)" "" "10";
         t "minus_nest" "(6 - 2) - (3 - 10)" "" "11";
         t "minus_nest_zero" "(1 - 2) - (3 - 4)" "" "0";
         t "minus_nest_plus" "(6 - 2) + (3 - 10)" "" "-3";
         t "mix_ops" "(2 - 3) + (4 * 5)" "" "19";
         t "mix_nested" "(1 + (2 + 3)) * ((4 - 5) - (1 * 5))" "" "-36";
         t "isnum_in_plus" "isnum(3 + (5 + 6))" "" "true";
         t "not_isnum_in_plus" "!(isnum(3 + (5 + 6)))" "" "false";
         t "isbool_in_plus" "isbool(3 + (5 + 6))" "" "false";
         t "not_isbool_in_plus" "!(isbool(3 + (5 + 6)))" "" "true";
         te "plus_overflow" "4611686018427387100 + 1000" "" "overflow";
         te "minus_overflow" "-4611686018427387100 - 1000" "" "overflow";
         te "times_overflow" "4611686018427387100 * 2" "" "overflow";
         te "plus_bool_r" "3 + true" "" "arithmetic expected a number";
         te "plus_bool_l" "true + 3" "" "arithmetic expected a number";
         te "minus_bool_r" "3 - true" "" "arithmetic expected a number";
         te "minus_bool_l" "true - 3" "" "arithmetic expected a number";
         te "times_bool_r" "3 * true" "" "arithmetic expected a number";
         te "times_bool_l" "true * 3" "" "arithmetic expected a number";
         t "or_true_true" "true || true" "" "true";
         t "or_true_false" "true || false" "" "true";
         t "or_false_true" "false || true" "" "true";
         t "or_false_false" "false || false" "" "false";
         t "or_short" "true || 1" "" "true";
         t "or_short_negated" "!(false) || 1" "" "true";
         t "or_short_print" "true || print(false)" "" "true";
         te "or_num_l" "2 || false" "" "logic expected a boolean";
         te "or_num_r" "false || 5" "" "logic expected a boolean";
         t "and_with_isnum_true" "isnum(5) && isnum(3)" "" "true";
         t "and_with_isnum_false" "isnum(5) && isnum(false)" "" "false";
         t "and_with_is_true" "isnum(5) && isbool(false)" "" "true";
         t "and_with_is_false" "isnum(5) && isbool(3)" "" "false";
         t "and_true_true" "true && true" "" "true";
         t "and_true_false" "true && false" "" "false";
         t "and_false_true" "false && true" "" "false";
         t "and_false_false" "false && false" "" "false";
         t "and_short" "false && 1" "" "false";
         t "and_short_negated" "!(true) && 1" "" "false";
         t "and_short_print" "false && print(false)" "" "false";
         t "and_short_let" "let x = false in x && print(2)" "" "false";
         t "and_short_let_both" "let x = false, y = print(2) in x && y" "" "2\nfalse";
         te "and_num_l" "2 && false" "" "logic expected a boolean";
         te "and_num_r" "true && 5" "" "logic expected a boolean";
         t "and_with_isnum_true" "isnum(5) && isnum(3)" "" "true";
         t "and_with_isnum_false" "isnum(5) && isnum(false)" "" "false";
         t "and_with_is_true" "isnum(5) && isbool(false)" "" "true";
         t "and_with_is_false" "isnum(5) && isbool(3)" "" "false";
         t "or_with_isnum_true" "isnum(5) || isnum(3)" "" "true";
         t "or_with_isnum_false_r" "isnum(5) || isnum(false)" "" "true";
         t "or_with_is_true" "isnum(5) || isbool(false)" "" "true";
         t "or_with_is_false" "isbool(5) || isbool(3)" "" "false";
         t "mixed_bools_false" "true && (false || (true && false))" "" "false";
         t "mixed_bools_true" "true && (false || (true && true))" "" "true";
         t "greater_1_1" "1 > 1" "" "false";
         t "greater_2_1" "2 > 1" "" "true";
         t "greater_neg_2_1" "-2 > 1" "" "false";
         t "greater_binop_false" "(5 + 1) > (6 * 2)" "" "false";
         t "greater_binop_true" "(5 * 3) > (6 * 2)" "" "true";
         te "greater_l_bool" "4 > false" "" "comparison expected a number";
         te "greater_r_bool" "false > 4" "" "comparison expected a number";
         t "greatereq_0_1" "0 >= 1" "" "false";
         t "greatereq_1_1" "1 >= 1" "" "true";
         t "greatereq_2_1" "2 >= 1" "" "true";
         t "greatereq_neg_2_1" "-2 >= 1" "" "false";
         t "greatereq_binop_false" "(5 + 1) >= (6 * 2)" "" "false";
         t "greatereq_binop_true" "(5 * 3) >= (6 * 2)" "" "true";
         te "greatereq_l_bool" "4 >= false" "" "comparison expected a number";
         te "greatereq_r_bool" "false >= 4" "" "comparison expected a number";
         t "less_1_1" "1 < 1" "" "false";
         t "less_1_2" "1 < 2" "" "true";
         t "less_neg_2_1" "-2 < 1" "" "true";
         t "less_binop_false" "(5 + 1) < (6 * 2)" "" "true";
         t "less_binop_true" "(5 * 3) < (6 * 2)" "" "false";
         te "less_l_bool" "4 < false" "" "comparison expected a number";
         te "less_r_bool" "false < 4" "" "comparison expected a number";
         t "lesseq_1_0" "1 <= 0" "" "false";
         t "lesseq_0_1" "0 <= 1" "" "true";
         t "lesseq_1_1" "1 <= 1" "" "true";
         t "lesseq_1_2" "1 <= 2" "" "true";
         t "lesseq_bigs" "4611686018427387100 <= 4611686018427387105" "" "true";
         t "lesseq_neg_2_1" "-2 <= 1" "" "true";
         t "lesseq_binop_false" "(5 + 1) <= (6 * 2)" "" "true";
         t "lesseq_binop_true" "(5 * 3) <= (6 * 2)" "" "false";
         te "lesseq_l_bool" "4 <= false" "" "comparison expected a number";
         te "lesseq_r_bool" "false <= 4" "" "comparison expected a number";
         t "eq_1_1" "1 == 1" "" "true";
         t "eq_1_0" "1 == 0" "" "false";
         t "eq_true_true" "true == true" "" "true";
         t "eq_false_true" "false == true" "" "false";
         t "eq_true_false" "true == false" "" "false";
         t "eq_false_false" "false == false" "" "true";
         t "eq_polymorphic" "4 == true" "" "false";
         t "comp_complex" "(4 > 5) || (1 == 1 && !(5 == 3))" "" "true";
         t "let_comp" "let x = 5, y = 10 in x < y" "" "true";
         t "let_comp_bindings" "let x = (5 == 5), y = (1 < 4) in x && y" "" "true";
         t "let_nested_comps"
           "let x = (6 > 4) in let y = ((2 == 2) && x) in y && (isnum(x) || isbool(y))" "" "true";
         t "if_true" "if true: 4 else: 2" "" "4";
         t "if_false" "if false: 4 else: 2" "" "2";
         t "if_let_cond" "if (let x = true in x): 4 else: 1" "" "4";
         t "if_let_then" "if true: (let x = 30 in x) else: 1" "" "30";
         t "if_let_else" "if false: 2 else: (let x = 12 in x)" "" "12";
         t "if_in_plus" "(if false: 4 else: 5) + (if true: 10 else: 2)" "" "15";
         t "if_in_lets"
           "(let x = (if true: 5 + 5 else: 6 * 2) in (let y = (if true: x * 3 else: x + 5) in y))"
           "" "30";
         t "if_isnum_cond" "if isnum(2 + 4): 5 else: false" "" "5";
         t "if_isnum_cond_short" "if isnum(false && 5): 5 else: false" "" "false";
         t "if_isbool_cond" "if isbool(true): 5 else: false" "" "5";
         t "if_isbool_cond_short" "if isbool(false && 5): 5 else: false" "" "5";
         t "if_numcomp_false" "if (4 > 5): 2 else: 3" "" "3";
         t "if_numcomp_true" "if (4 < 5): 2 else: 3" "" "2";
         t "if_numcomp_branch_else" "if false: (3 > 4) else: (1 == 1)" "" "true";
         t "if_numcomp_branch_then" "if true: (3 > 4) else: (1 == 1)" "" "false";
         t "if_short" "if (true || 1337): (false && 1729) else: 4" "" "false";
         t "if_print_then" "if print(true): print(4) + 10 else: print(3)" "" "true\n4\n14";
         t "if_print_else" "if print(false): print(4) else: print(3) * 2" "" "false\n3\n6";
         t "if_in_ifs" "if false: (if false: 1 else: 2) else: 3" "" "3";
         te "lexer_error" "let $ = 5 in $" "" "Unrecognized character: $";
         te "parse_error" "def g(x): 5 + x" "" "Parse error at line 1, col 15: token ``";
         te "if_not_boolean_cond" "if 10: 5 else: 3" "" "if expected a boolean";
         te "free_id_plain" "x" ""
           "The identifier x, used at <free_id_plain, 1:0-1:1>, is not in scope";
         te "free_id_recursive" "let x = x + 5 in x" ""
           "The identifier x, used at <free_id_recursive, 1:8-1:9>, is not in scope";
         te "dup_id" "let x = 5, x = 2 in x" ""
           "The identifier x, redefined at <dup_id, 1:11-1:12>, duplicates one at <dup_id, 1:4-1:5>";
         te "dup_id_multiple" "let x = 5, x = 2, x = 3 in x" ""
           "The identifier x, redefined at <dup_id_multiple, 1:18-1:19>, duplicates one at \
            <dup_id_multiple, 1:11-1:12>\n\
            The identifier x, redefined at <dup_id_multiple, 1:11-1:12>, duplicates one at \
            <dup_id_multiple, 1:4-1:5>";
         te "dup_fun" "def f(x): x + y\ndef f(x, y): 5 + x + y\nf(1)" ""
           "The identifier y, used at <dup_fun, 1:14-1:15>, is not in scope";
         te "unbound_fun" "f(7)" ""
           "The identifier f, used at <unbound_fun, 1:0-1:1>, is not in scope";
         te "unbound_fun_in_fun" "def f(x): g(x)\nf(5)" ""
           "The identifier g, used at <unbound_fun_in_fun, 1:10-1:11>, is not in scope";
         te "overflow" "4611686018427387999" "" "overflow";
         te "underflow" "-4611686018427387999" "" "underflow";
         te "arity_low" "def f(x, y): x + y\nf(2)" ""
           "expected an arity of 2, but received 1 arguments";
         te "arity_high" "def f(x): x + y\nf(2, 2)" ""
           "expected an arity of 1, but received 2 arguments";
         te "lots_of_errors"
           "def f(x): y + g(k)\ndef f(y): x + 4611686018427387999\n let x = x + f(x, 3) in g(x)" ""
           "The identifier g, used at <lots_of_errors, 3:24-3:25>, is not in scope\n\
            The identifier x, used at <lots_of_errors, 3:9-3:10>, is not in scope\n\
            The function called at <lots_of_errors, 3:13-3:20> expected an arity of 1, but \
            received 2 arguments\n\
            The identifier x, used at <lots_of_errors, 3:15-3:16>, is not in scope\n\
            The identifier y, used at <lots_of_errors, 1:10-1:11>, is not in scope\n\
            The identifier g, used at <lots_of_errors, 1:14-1:15>, is not in scope\n\
            The identifier k, used at <lots_of_errors, 1:16-1:17>, is not in scope\n\
            The identifier x, used at <lots_of_errors, 2:10-2:11>, is not in scope\n\
            The number literal 4611686018427387999, used at <lots_of_errors, 2:14-2:33>, is not \
            supported in this language";
         t "def_f_of_x" "def f(x): x\nf(5)" "" "5";
         t "def_f_of_x_y" "def f(x, y): x + y\nf(5, 2)" "" "7";
         t "def_f_of_x_def_g_of_x" "def f(x): x\ndef g(x): x\nf(4)+g(5)" "" "9";
         t "fact" "def fact(n): if n == 1: 1 else: n * fact(n - 1)\n fact(5)" "" "120";
         t "fact_tail"
           "def fact_tail(n, acc):\n\
            if n <= 1: acc\n\
            else: fact_tail(n - 1, n * acc)\n\
            fact_tail(4, 1)" "" "24";
         t "def_with_lets" "def f(x): (let a = x, b = a, c = a + b in c)\nf(100)" "" "200";
         t "def_with_ifs" "def f(x): x + (if true: let y = x in y else: 12)\nf(4)" "" "8";
         t "def_with_print" "def f(x): print(x) + 2\n print(f(5)) + 2" "" "5\n7\n9";
         t "def_with_bool" "def f(cond): if cond: 5 else: 10\n f(false)" "" "10";
         t "def_big_int" "def f(x): x + 3000\nf(1611686018427387999)" "" "1611686018427390999";
         t "call_in_let_body" "def f(x, y): x * y\nlet x = 5, y = 2 in f(x, y)" "" "10";
         t "call_in_let_binding" "def f(x, y): x * y\nlet x = f(3, 5) in x" "" "15";
         tvg "call_in_let_binding_valgrind" "def f(x, y): x * y\nlet x = f(3, 5) in x" "" "15";
         t "call_in_let_binding_op" "def f(x, y): x * y\nlet x = f(3, 5) in x + 10" "" "25";
         t "call_in_let_binding_with_bindings"
           "def f(x, y): x * y\nlet x = 10, y = 5 in let z = f(x, y) in z" "" "50";
         t "call_nested_ops" "def f(x): x + x\nf((2 * 2) - (2 * 3))" "" "-4";
         tvg "call_nested_ops_valgrind" "def f(x): x + x\nf((2 * 2) - (2 * 3))" "" "-4";
         t "def_nested_ops" "def f(x): (x + 5) - (2 * x)\nf(3)" "" "2";
         t "decl_with_and" "def f(x): (x && true)\nf(false)" "" "false";
         t "decl_with_or" "def f(x): (x || true)\nf(false)" "" "true";
         t "and_function_app" "def f(): true\n def g(): false\nf() && g()" "" "false";
         t "or_function_app" "def f(): true\n def g(): false\nf() || g()" "" "true";
         tvg "max_rec_1_valgrind" "def max(x, y):\n  if y >= x: y\n  else: max(y, x)\nmax(9, 6)" ""
           "9";
         tvg "max_rec_2_valgrind" "def max(x, y):\n  if y >= x: y\n  else: max(y, x)\nmax(6, 9)" ""
           "9";
         t "max_rec_1" "def max(x, y):\n  if y >= x: y\n  else: max(y, x)\nmax(9, 6)" "" "9";
         t "max_rec_2" "def max(x, y):\n  if y >= x: y\n  else: max(y, x)\nmax(6, 9)" "" "9";
         t "max_rec_1_in_let"
           "def max(x, y):\n  if y >= x: y\n  else: let i = x, k = y in max(k, i)\nmax(9, 6)" "" "9";
         t "max_rec_2_in_let"
           "def max(x, y):\n  if y >= x: y\n  else: let i = y in max(i, x)\nmax(6, 9)" "" "9";
         tvg "max_rec_1_in_let_valgrind"
           "def max(x, y):\n  if y >= x: y\n  else: let i = x, k = y in max(k, i)\nmax(9, 6)" "" "9";
         tvg "max_rec_2_in_let_valgrind"
           "def max(x, y):\n  if y >= x: y\n  else: let i = y in max(i, x)\nmax(6, 9)" "" "9";
         t "tail_bool" "def f(b): if b: 1337 else: f(!(b))\nf(false)" "" "1337";
         tvg "tail_bool_valgrind" "def f(b): if b: 1337 else: f(!(b))\nf(false)" "" "1337";
         t "tail_bool_mul_args"
           "def f(b1, b2, b3): if b1 && (b2 || b3): 1337 else: f(!(b1), !(b2), b2 || b1)\n\
            f(true, false, false)" "" "1337";
         tvg "tail_bool_mul_args_valgrind"
           "def f(b1, b2, b3): if b1 && (b2 || b3): 1337 else: f(!(b1), !(b2), b2 || b1)\n\
            f(true, false, false)" "" "1337";
         t "fibonacci_normal_rec" "def fib(n): if n < 2: n else: fib(n - 1) + fib(n - 2)\nfib(6)" ""
           "8";
         t "nil" "nil" "" "nil";
         t "empty" "let t = () in t" "" "()";
         t "tup_1el" "let t = (1,) in t" "" "(1, )";
         t "tup_2el" "let t = (1, 2) in t" "" "(1, 2)";
         t "tup_3el" "let t = (1, 2, 3) in t" "" "(1, 2, 3)";
         t "tup_nested" "let t = (1, (2, 3), 4) in t" "" "(1, (2, 3), 4)";
         t "tup_bools" "let t = (true, false) in t" "" "(true, false)";
         t "tup_evaluation_order_prints" "(print(1), print(2), print(3))" "" "1\n2\n3\n(1, 2, 3)";
         t "tup_nils" "let t = (nil, nil, nil) in t" "" "(nil, nil, nil)";
         t "tup_polymorphic"
           "let x = 5, t1 = (1, false), t2 = (true, (x, 4, nil), false, 2, t1) in t2" ""
           "(true, (5, 4, nil), false, 2, (1, false))";
         t "tup_with_binding" "let x = 5, y = 2 in let t = (x, (y, 9)) in t" "" "(5, (2, 9))";
         t "print_tup" "print((1, 2, 3))" "" "(1, 2, 3)\n(1, 2, 3)";
         t "tup_def" "def f(x): let t = (x, 2, x + 4) in t\nf(3)" "" "(3, 2, 7)";
         te "redef_builtin_1" "def our_code_starts_here(): 1\n1" ""
           "The function name our_code_starts_here, redefined at <redef_builtin_1, 1:0-1:29>, \
            duplicates one at <, 0:-1-0:-1>";
         te "redef_builtin_2" "def equal(x, y): 1\n1" ""
           "The function name equal, redefined at <redef_builtin_2, 1:0-1:18>, duplicates one at \
            <, 0:-1-0:-1>";
         te "redef_builtin_3" "def print(x): 1\n1" ""
           "The function name print, redefined at <redef_builtin_3, 1:0-1:15>, duplicates one at \
            <, 0:-1-0:-1>";
         te "redef_builtin_4" "def print(x, y): 1\n1" ""
           "The function name print, redefined at <redef_builtin_4, 1:0-1:18>, duplicates one at \
            <, 0:-1-0:-1>";
         t "istup_true_lit" "istuple((1, 2, 3))" "" "true";
         t "istup_true_nil" "istuple(nil)" "" "true";
         t "istup_true_empty" "istuple(())" "" "true";
         t "istup_false_num" "istuple(5)" "" "false";
         t "istup_false_boolfalse" "istuple(false)" "" "false";
         t "istup_false_booltrue" "istuple(true)" "" "false";
         t "istup_true_let" "let x = (1, 2) in istuple(x)" "" "true";
         t "set_tup_get_set_value" "let tup = (1, 2, 3) in tup[2] := (3, 4); tup[2]" "" "(3, 4)";
         t "set_tup_get_other_value" "let tup = (1, 2, 3) in tup[2] := (3, 4); tup[1]" "" "2";
         t "tup_access_lit_0" "(6, 10, 17)[0]" "" "6";
         t "tup_access_bind_0" "let t = (6, 10, 17) in t[0]" "" "6";
         t "tup_access_lit_1" "(6, 10, 17)[1]" "" "10";
         t "tup_access_bind_1" "let t = (6, 10, 17) in t[1]" "" "10";
         t "tup_access_lit_2" "(6, 10, 17)[2]" "" "17";
         t "tup_access_bind_2" "let t = (6, 10, 17) in t[2]" "" "17";
         t "tuple_bind_same_let" "let x = (1, 2, 3), (a, b, c) = x in a" "" "1";
         t "tuple_access_nested_forward" "let t = (1, (2, (3, (4, (5,))))) in t[1][1][1][1][0]" ""
           "5";
         t "tuple_access_nested_backwards" "let t = (((((5,), 4), 3), 2), 1) in t[0][0][0][0][0]" ""
           "5";
         t "tuple_access_good_from_access" "let bs = (true, false), nums = (1, 2, 3) in bs[nums[0]]"
           "" "false";
         te "tuple_access_bad1_from_access"
           "let bs = (true, false), nums = (1, 2, 3) in bs[nums[1]]" "" "index too large";
         te "tuple_access_bad2_from_access"
           "let bs = (true, false), nums = (1, 2, 3) in nums[bs[1]]" "" "get expected numeric index";
         te "tuple_access_bad3_from_access"
           "let bs = (true, false), nums = (1, 2, 3) in nums[bs[2]]" "" "index too large";
         te "bad_tuple_bind" "let (a, b, c) = (1, 2) in c" "" "a tuple was badly destructed";
         te "bad_tuple_nest" "let (a, (b, c), d) = (1, 2, 3) in b" "" "a tuple was badly destructed";
         te "tup_access_indexnotnum" "(1,2)[false]" "" "get expected numeric index";
         te "tup_access_nil" "nil[1]" "" "tried to access component of nil";
         te "tup_access_low" "(1, 2, 3)[-1]" "" "index too small";
         te "tup_access_high" "(3, 4, 2)[3]" "" "index too large";
         te "tup_access_empty_low" "()[-1]" "" "index too small";
         te "tup_access_empty_high" "()[0]" "" "index too large";
         te "def_tup_access_bad"
           "def f(t, i): t[i]\ndef ez(i): (1, 2, 3, 4, 5)\n ez(0) + ez(1) + ez(2) + ez(3) + ez(4)"
           "" "arithmetic expected a number";
         t "tup_eq_false" "(1, 2, 3) == (1, 2, 3)" "" "false";
         t "tup_eq_true" "let x = (1, 2, 3) in x == x" "" "true";
         t "tup_eq_true_mult" "let x = (1, 2, 3), y = x in x == y" "" "true";
         t "tup_eq_access_true" "let x = (1, 2, 3) in x[1] == 2" "" "true";
         t "seq_inside_let_binding" "let x = (1; 2) in x" "" "2";
         t "given_tup1"
           "let t = (4, (5, 6)) in\n\
           \            begin\n\
           \              t[0] := 7;\n\
           \              t\n\
           \            end" "" "(7, (5, 6))";
         t "given_tup2"
           "let t = (4, (5, nil)) in\n\
           \            begin\n\
           \              t[1] := nil;\n\
           \              t\n\
           \            end" "" "(4, nil)";
         t "cyclic_tuple_1"
           "let t = (4, (5, nil)) in\n\
           \            begin\n\
           \              t[1] := t;\n\
           \              t\n\
           \            end" "" "(4, <cyclic tuple 1>)";
         t "cyclic_tuple_2"
           "let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; (t1, t2)" ""
           "((1, (<cyclic tuple 2>, 5, 6), 3), ((1, <cyclic tuple 4>, 3), 5, 6))";
         tvg "cyclic_tuple_2_valgrind"
           "let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; (t1, t2)" ""
           "((1, (<cyclic tuple 2>, 5, 6), 3), ((1, <cyclic tuple 4>, 3), 5, 6))";
         t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))";
         t "given_ex_1" "let t = (3, ((4, true), 5)) in\nlet (x, (y, z)) = t in\nx + y[0] + z" ""
           "12";
         t "given_ex_2"
           "let three  = (0, 0, 0) in\n\
            let three1 = three[0] := 1 in\n\
            let three2 = three[1] := 2 in\n\
            three[2] := 3; three" "" "(1, 2, 3)";
         t "given_ex_3"
           "let three  = (0, 0, 0) in\n\
            let three1 = three[0] := 1 in\n\
            let three2 = three[1] := 2 in\n\
            three[2] := 3;\n\
            print(three);\n\
            # Now three equals (1, 2, 3), three1 == 1 and three2 == 2\n\n\
            let pair = (5, 6) in\n\
            pair[1] := three[1] := 10;\n\
            print(three);\n\
            pair"
           "" "(1, 2, 3)\n(1, 10, 3)\n(5, 10)";
         (* NOTE: set returns value at idx, not whole tuple *)
         t "set_tup" "(1, 2, 3)[2] := (3, 4)" "" "(3, 4)";
         t "set_tup_bind" "let t = (1, 2, 3) in t[0] := 3; t" "" "(3, 2, 3)";
         te "set_tup_index_large" "let t = (1, 2, 3) in t[3] := 4; t" "" "index too large";
         te "set_tup_index_small" "let t = (1, 2, 3) in t[-1] := -1; t" "" "index too small";
         te "set_tup_index_not_num" "let t = (1, 2, 3) in t[false] := true; t" ""
           "set expected numeric index";
         t "set_nil" "let t = (1, (2, 3)) in t[1] := nil; t[1] := 3; t" "" "(1, 3)";
         te "set_nil_deref" "let t = (1, (2, 3)) in t[1] := nil; t[1][0] := 3; t" ""
           "tried to access component of nil";
         te "set_not_tuple" "true[1] := 4" "" "set expected tuple";
         t "def_set_swap_good"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\n\
            swap((1, 2, 3, 4), 0, 3)" "" "(4, 2, 3, 1)";
         tvg "def_set_swap_good_valgrind"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\n\
            swap((1, 2, 3, 4), 0, 3)" "" "(4, 2, 3, 1)";
         te "def_set_swap_bad1"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\n\
            swap((1, 2, 3), 0, 3)" "" "index too large";
         te "def_set_swap_bad2"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\nswap(nil, 0, 3)" ""
           "component of nil";
         te "def_set_swap_bad3"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\nswap(false, 0, 3)"
           "" "get expected tuple";
         te "def_set_swap_bad4"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\n\
            swap((1, 2, 3), -1, 2)" "" "index too small";
         te "def_set_swap_bad5"
           "def swap(t, x, y): let temp = t[y] in t[y] := t[x]; t[x] := temp; t\n\
            swap((1, 2, 3), 0, 4)" "" "index too large";
         t "def_tup_lit"
           "def add_pairs((x1, y1), (x2, y2)): (x1 + x2, y1 + y2)\nadd_pairs((5, 8), (5, 12))" ""
           "(10, 20)";
         t "def_tup_bind"
           "def add_pairs((x1, y1), (x2, y2)): (x1 + x2, y1 + y2)\n\
            let x = (6, 12), y = (3, 4) in add_pairs(x, y)" "" "(9, 16)";
         t "def_tup_get_at_input" "def f(): input() + input()\nf()" "5\n10" "15";
         t "def_tup_get_at_input_into_tup" "def f(): (input(),  input())\nf()" "5\n10" "(5, 10)";
         t "def_tup_print_into_tup1" "def f(x, y): (print(x), print(y))\nf(10, 20)" ""
           "10\n20\n(10, 20)";
         t "def_tup_print_into_tup2"
           "def f(x, y, z, a, b): (print(x), print(y), print(z), print(a), print(b))\n\
            f(10, 20, 30, 40, 50)" "" "10\n20\n30\n40\n50\n(10, 20, 30, 40, 50)";
         t "input_num_pos" "input()" "14" "14";
         t "input_num_neg" "input()" "-6" "-6";
         t "input_num_true" "input()" "true" "true";
         t "input_num_false" "input()" "false" "false";
         t "input_max" "input()" "4611686018427387903" "4611686018427387903";
         t "input_min" "input()" "-4611686018427387904" "-4611686018427387904";
         t "input_zero" "input()" "0" "0";
         te "input_bad" "input()" "blah" "Input wasn't given a valid snakeval";
         te "input_bad_with_nums" "input()" "blah 123" "Input wasn't given a valid snakeval";
         te "input_overflow" "input()" "4611686018427387904" "Input wasn't given a valid snakeval";
         te "input_underflow" "input()" "-4611686018427387905" "Input wasn't given a valid snakeval";
         te "input_tuple" "input()" "(1, 2, 3)" "Input wasn't given a valid snakeval";
         t "input1" "let x = input() in x + 2" "123" "125";
         t "input_into_tuple" "let t = (input(), input(), input()) in t" "1\n2\n3" "(1, 2, 3)";
         t "input_into_tuple_from_funcs"
           "def a(): input()\ndef b(): input()\ndef c(): input()\nlet t = (a(), b(), c()) in t"
           "1\n2\n3" "(1, 2, 3)";
         t "equal_num_true" "equal(6, 6)" "" "true";
         t "equal_num_false" "equal(6, 7)" "" "false";
         t "equal_bool_true1" "equal(true, true)" "" "true";
         t "equal_bool_true2" "equal(false, false)" "" "true";
         t "equal_bool_false1" "equal(true, false)" "" "false";
         t "equal_bool_false2" "equal(false, true)" "" "false";
         t "equal_nil_false" "equal(nil, true)" "" "false";
         t "equal_nil_true" "equal(nil, nil)" "" "true";
         t "equal_nil_num" "equal(nil, 5)" "" "false";
         t "equal_num_false" "equal(7, true)" "" "false";
         t "equal_tup_true1" "equal((1, 2), (1, 2))" "" "true";
         t "equal_tup_true2" "equal((), ())" "" "true";
         t "equal_tup_false1" "equal((), nil)" "" "false";
         t "equal_tup_false2" "equal((1,), nil)" "" "false";
         t "equal_tup_false3" "equal((), (1,))" "" "false";
         t "equal_tup_nested_true1" "equal((1, (3, 5)), (1, (3, 5)))" "" "true";
         t "equal_tup_nested_false1" "equal((1, (3, 5)), (1, (3, 9)))" "" "false";
         t "equal_tup_nested_false2" "equal((1, (3, 5)), (1, 3, 9))" "" "false";
         t "equal_tup_nested_false3" "equal((1, (3, 5)), (1, (9,)))" "" "false";
         t "equal_tup_id_true"
           "let x = (1, (7, 9), (2, 4)), y = (1, (7, 9), (2, 4)) in (equal(x, y))" "" "true";
         t "equal_tup_id_false"
           "let x = (1, (7, 9), (2, 4)), y = (1, (7, x), (2, 4)) in (equal(x, y))" "" "false";
         t "equal_cyclic_tuple_1"
           "let t = (4, (5, nil)) in\n\
           \            begin\n\
           \              t[1] := t;\n\
           \              equal(t, t)\n\
           \            end" "" "true";
         t "equal_cyclic_tuple_2"
           "let t1 = (4, (5, nil)), t2 = (4, (5, nil)) in\n\
           \            begin\n\
           \              t1[1] := t2;\n\
           \              t2[1][1] := t1;\n\
           \              equal(t1, t2)\n\
           \            end" "" "false";
         tvg "equal_cyclic_tuple_2_valgrind"
           "let t1 = (4, (5, nil)), t2 = (4, (5, nil)) in\n\
           \            begin\n\
           \              t1[1] := t2;\n\
           \              t2[1][1] := t1;\n\
           \              equal(t1, t2)\n\
           \            end" "" "false";
         t "equal_from_funcs_true" "def f(): (1, 2, 3)\ndef g(): (1, 2, 3)\nequal(f(), g())" ""
           "true";
         t "equal_from_funcs_false" "def f(): (1, 2, 5)\ndef g(): (1, 2, 3)\nequal(f(), g())" ""
           "false";
         t "equal_from_funcs_params_true"
           "def f(x): (1, x, 5)\ndef g(x, y): (1, x, y)\nequal(f(2), g(2, 5))" "" "true";
         t "equal_from_funcs_params_false"
           "def f(x): (1, x, 5)\ndef g(x, y): (1, x, y)\nequal(f(2), g(1, 5))" "" "false";
         t "equal_but_not_addr"
           "let t1 = (1, 2, 3), t2 = (1, 2, 3) in print(equal(t1, t2)); t1 == t2" "" "true\nfalse";
         t "equal_and_eq_addr" "let t1 = (1, 2, 3), t2 = t1 in print(equal(t1, t2)); t1 == t2" ""
           "true\ntrue";
         t "tup_defs_tail"
           "def g(x, y): (x + y, x - y)\n\
           \            let rec f = (lambda ((x, y), z): let t = (x, y + z) in g(t[0], t[1])) in\n\
            f((5, 5), 2)" "" "(12, -2)";
         te "tup_destruct_bad1" "let (a, b) = (1,) in a" "" "a tuple was badly destructed";
         te "tup_destruct_bad2" "let ((l), c) = (1, 2) in c" "" "a tuple was badly destructed";
         te "tup_destruct_bad3" "let ((a, b, c), d) = (3, 5) in a" "" "a tuple was badly destructed";
         te "tup_destruct_bad4" "let ((a, b), c, d) = (1, 2) in a" "" "a tuple was badly destructed";
         te "tup_destruct_bad5" "let ((a, b, c), d) = (1,) in a" "" "a tuple was badly destructed";
         te "let_tup_destruct_bad" "let t = (1, 2, 3) in let (a, (b, c)) = t in t" ""
           "a tuple was badly destructed";
         te "let_tup_access_input_bad1" "let t = (1, 2, 3) in t[input()]" "3" "index too large";
         te "let_tup_access_input_bad2" "let t = (1, 2, 3) in t[input()]" "-1" "index too small";
         te "let_tup_access_input_bad3" "let t = (1, 2, 3) in t[input()]" "true"
           "get expected numeric index";
         t "let_tup_access_input_good" "let t = (1, 2, 3) in t[input()]" "1" "2";
         t "def_tup_destruct_good" "def f(x): let (a, b, c) = x in a + b + c\nf((1, 2, 3))" "" "6";
         te "def_tup_destruct_wrong_size_1" "def f(x): let (a, b, c) = x in a + b + c\nf((1, 3))" ""
           "a tuple was badly destructed";
         te "def_tup_destruct_wrong_size_2" "def f(x): let (a, b, c) = x in a + b + c\nf((1))" ""
           "a tuple was badly destructed";
         te "def_tup_destruct_boolean" "def f(x): let (a, b, c) = x in a + b + c\nf(true)" ""
           "a tuple was badly destructed";
         te "def_tup_destruct_number" "def f(x): let (a, b, c) = x in a + b + c\nf(1)" ""
           "a tuple was badly destructed";
         te "def_tup_destruct_nil" "def f(x): let (a, b, c) = x in a + b + c\nf(nil)" ""
           "a tuple was badly destructed";
         te "destruct_duplicate" "let (a, b, (b, c)) = (1, 2, (3, 4)) in c" ""
           "The identifier b, redefined at <destruct_duplicate, 1:8-1:9>, duplicates one at \
            <destruct_duplicate, 1:12-1:13>";
         t "seq_lit" "4;2" "" "2";
         t "seq_let_input" "let x = input() in print(x);false" "true" "true\nfalse";
         t "seq_let_tup_set" "let t = (1, 2, 3) in t[2] := 10; t" "" "(1, 2, 10)";
         t "seq_in_def" "def f(x, y): print(input() + x); y\nf(5, 2)" "3" "8\n2";
         t "sum_til_false"
           "def sum(t, i): if t[i] == false: 0 else: t[i] + sum(t, i + 1)\n\
            sum((2, 2, 2, 2, false),0)" "" "8";
         t "blank_in_decl" "def f(a, _, c): a + c\nf(1, false, 3)" "" "4";
         t "blank_in_decl2" "def f(a, _, _, _, c): a  + c\nf(1, false, true, (1, 2), 3)" "" "4";
         t "blank_in_decl_tuple_lit"
           "def f((a, _), (b, (_, c))): a + b + c\nf((4, 3), (5, (10, 9)))" "" "18";
         t "blank_in_decl_tuple_binds"
           "def f((a, _), (b, (_, c))): a + b + c\nlet t1 = (4, 3), t2 = (5, (10, 9)) in f(t1, t2)"
           "" "18";
         t "blank_in_decl_tuple_binds_blanks"
           "def f((a, _), (b, (_, c))): a + b + c\n\
            let t1 = (4, 3), t2 = (5, (10, 9)) in let (a, _) = t1, (b, (_, c)) = t2 in f((a, 1), \
            (b, (1, c)))"
           "" "18";
         t "testarg" "testarg(1, 2, 3, 4, 5, 6, 7, 8, 9)" "" "1\n2\n3\n4\n5\n6\n7\n8\n9\nfalse";
         t "testarg_print"
           "testarg(print(1), print(2), print(3), print(4), print(5), print(6), print(7), \
            print(8), print(9))"
           "" "1\n2\n3\n4\n5\n6\n7\n8\n9\n1\n2\n3\n4\n5\n6\n7\n8\n9\nfalse";
         te "tuple_binop" "(1, 2) + (3, 5)" "" "arithmetic expected a number";
         te "tuple_unary" "add1((3, 5))" "" "arithmetic expected a number";
         te "tuple_duplicate_destruct" "let (a, b, b) = (1, 2, 3) in a" ""
           "The identifier b, redefined at <tuple_duplicate_destruct, 1:8-1:9>, duplicates one at \
            <tuple_duplicate_destruct, 1:11-1:12>";
         te "def_tuple_duplicate1" "def f((a, b), b): 1\n1" ""
           "The identifier b, redefined at <def_tuple_duplicate1, 1:10-1:11>, duplicates one at \
            <def_tuple_duplicate1, 1:14-1:15>";
         te "def_tuple_duplicate2" "def f((a, b), (b, c)): 1\n1" ""
           "The identifier b, redefined at <def_tuple_duplicate2, 1:10-1:11>, duplicates one at \
            <def_tuple_duplicate2, 1:15-1:16>";
         te "def_tuple_duplicate3" "def f((a, b, b)): 1\n1" ""
           "The identifier b, redefined at <def_tuple_duplicate3, 1:10-1:11>, duplicates one at \
            <def_tuple_duplicate3, 1:13-1:14>";
         te "def_tuple_duplicate4" "def f((a, b, (c, b))): 1\n1" ""
           "The identifier b, redefined at <def_tuple_duplicate4, 1:10-1:11>, duplicates one at \
            <def_tuple_duplicate4, 1:17-1:18>";
         te "tuple_multiple_errs"
           "def f((a, b, b), a): a + d\nlet (a, b, c) = (1, 2, a), b = 4 in d" ""
           "The identifier d, used at <tuple_multiple_errs, 2:36-2:37>, is not in scope\n\
            The identifier b, redefined at <tuple_multiple_errs, 2:27-2:28>, duplicates one at \
            <tuple_multiple_errs, 2:8-2:9>\n\
            The identifier a, used at <tuple_multiple_errs, 2:23-2:24>, is not in scope\n\
            The identifier d, used at <tuple_multiple_errs, 1:25-1:26>, is not in scope\n\
            The identifier a, redefined at <tuple_multiple_errs, 1:7-1:8>, duplicates one at \
            <tuple_multiple_errs, 1:17-1:18>\n\
            The identifier b, redefined at <tuple_multiple_errs, 1:10-1:11>, duplicates one at \
            <tuple_multiple_errs, 1:13-1:14>";
         t "fibonacci_tup_acc_helper"
           "def fib_help(a, b, n):\n\
           \            if n == 0:\n\
           \              nil\n\
           \            else:\n\
           \              (a, fib_help(a + b, a, n - 1))\n\n\n\
           \          let fib = (lambda (n):\n\
           \           # put a + 0 to stop tail recursion on main function\n\
           \           fib_help(1, 0, n)) in fib(10)\n\n\
           \           " "" "(1, (1, (2, (3, (5, (8, (13, (21, (34, (55, nil))))))))))";
         te "nil_deref" "let t = nil in t[true]" "" "tried to access component of nil";
         te "let_tup_missing_binding1" "let (a, b) = (1, 2, 3) in (a, b)" ""
           "a tuple was badly destructed";
         te "let_tup_missing_binding2" "let t = (1, 2, 3) in let (a) = t in a" ""
           "a tuple was badly destructed";
         te "nested_lambda_get_tuple" "(lambda (x): (lambda (y, z): x + y + z))[1]" ""
           "get expected tuple";
         t "tuple_mutate_in_lambda"
           "let t = (1, 2) in let f = (lambda : t[1] := (t[1] + 1)) in f(); f(); f(); f(); t" ""
           "(1, 6)";
         t "let_rec_mutate_lambda"
           "let t = (1, 2) in let rec f = (lambda (n): if n == 0: t else: (t[0] := (t[0] + 1)); \
            f(n - 1)) in f(3)"
           "" "(4, 2)";
         t "def_add" "def f(): 30\ndef g(): 20\nf() + g()" "" "50";
         t "simple_mut_rec"
           "let rec f = (lambda (x) : if (x == 0): 0 else: g(x - 1)), g = (lambda (y): if (y == \
            0): 0 else: f(y - 1)) in f(5)"
           "" "0";
         t "mutual_rec_tail"
           "def f(x): g(x - 3) + 0 and def g(x): if x > 4: x else: f(x + 4) + 0\n f(20)" "" "17";
         tvg "mutual_rec_tail_valgrind"
           "def f(x): g(x - 3) + 0 and def g(x): if x > 4: x else: f(x + 4) + 0\n f(20)" "" "17" ]

let lambda_suite =
  "lambda_suite"
  >::: [ t "lambda_lit_one_arg_simple" "(lambda (x): x)" "" "(lambda (arity: 1): ... )";
         tvg "lambda_lit_one_arg_simple_valgrind" "(lambda (x): x)" "" "(lambda (arity: 1): ... )";
         t "lambda_lit_three_arg_simple" "(lambda (x, y, z): x + y + z)" ""
           "(lambda (arity: 3): ... )";
         t "lambda_empty_lit" "(lambda : 1)" "" "(lambda (arity: 0): ... )";
         t "print_lambda" "print((lambda (x): x));6" "" "(lambda (arity: 1): ... )\n6";
         t "lambda_lit_nested" "(lambda (x): (lambda (y): (lambda (z): x + y + z)))" ""
           "(lambda (arity: 1): ... )";
         t "lambda_lit_fv" "let y = 3 in (lambda (x): x + y)" "" "(lambda (arity: 1): ... 3 ... )";
         t "lambda_lit_fv_lambda" "let f = (lambda (x): x) in (lambda (_): f)" ""
           "(lambda (arity: 1): ... <closure fv: 0> ... )";
         t "lambda_lit_apply" "(lambda (x): x)(4)" "" "4";
         t "lambda_tuple_apply" "let t = (1, 2, 3) in (lambda ((x, y ,z)): x + y + z)(t)" "" "6";
         t "lambda_empty_lit_apply" "(lambda : 1)()" "" "1";
         te "not_lambda_apply" "(4 + 2)(3)" "" "tried to call a non-closure value";
         te "arity_lambda_apply" "(lambda (x): x)(3, 3)" "" "arity mismatch";
         t "lambda_lit_apply_twoargs" "(lambda (x, y): x + y)(4, 5)" "" "9";
         t "lambda_lit_apply_threeargs" "(lambda (x, y, z): x + y + z)(4, 5, 5)" "" "14";
         t "lambda_lit_apply_fourargs" "(lambda (x, y, z, w): x + y + z + w)(4, 5, 5, 5)" "" "19";
         t "lambda_lit_apply_fourargs_ignored" "(lambda (x, y, z, w): x + y + w)(1, 2, 3, 4)" "" "7";
         t "lambda_lit_apply_prim2" "(lambda (x): x + 5)(4)" "" "9";
         t "lambda_as_id" "let f = (lambda (x): x + 5) in f(4)" "" "9";
         t "lambda_a_freevar" "let x = 5, f = (lambda (y): x + y) in f(4)" "" "9";
         t "lambda_a_freevar_twoargs" "let x = 5, f = (lambda (y, z): x + y + z) in f(4, 4)" "" "13";
         t "even_free_vars_even_args"
           "let x = 1, y = 2, f = (lambda (a, b): a + b + x + y) in f(3, 4)" "" "10";
         t "even_free_vars_even_args_two"
           "let x = 1, y = 2, f = (lambda (a, b): a + b + x + y) in let x = 3, y = 4 in f(x, y)" ""
           "10";
         t "odd_free_vars_even_args"
           "let x = 1, y = 2, z = 3, f = (lambda (a, b, c, d): a + b + c + d + x + y + z) in\n\
           \          f(4, 5, 6, 7)" "" "28";
         t "even_free_vars_odd_args"
           "let x = 1, y = 2, z = 3, xx = 4, f = (lambda (a, b, c): a + b + c + x + y + z + xx) in\n\
           \          f(5, 6, 7)" "" "28";
         t "odd_free_vars_odd_args"
           "let x = 1, y = 2, z = 3, f = (lambda (a, b, c): a + b + c + x + y + z) in f(4, 5, 6)" ""
           "21";
         t "lambda_in_lambda" "(lambda (x): x + (lambda (y): y)(5))(4)" "" "9";
         t "lambda_in_lambda_mulargs"
           "(lambda (x, k): x + k + (lambda (y, j, h): y + j + h)(5, 3, 2))(4, 1)" "" "15";
         tvg "lambda_in_lambda_valgrind" "(lambda (x): x + (lambda (y): y)(5))(4)" "" "9";
         t "lambda_times_lambda" "(lambda (x): x + 2)(6) * (lambda (x): x + 1)(5)" "" "48";
         tvg "lambda_times_lambda_valgrind" "(lambda (x): x + 2)(6) * (lambda (x): x + 1)(5)" ""
           "48";
         t "lambda_in_lambda_fv" "(lambda (x): (lambda (y): y + x)(5))(4)" "" "9";
         t "lambdas_in_lambda_fv" "(lambda (x): (lambda (y): y + x)(5) + (lambda (y): y + x)(5))(4)"
           "" "18";
         t "lambdas_in_lambdas_fv"
           "(lambda (x): (lambda (x): (lambda (y): y + x)(5) + (lambda (y): y + x)(5))(4) + \
            (lambda (x): (lambda (y): y + x)(5) + (lambda (y): y + x)(5))(4))(4)"
           "" "36";
         t "lambda_cyclic_tuple_val"
           "let tlam = (lambda :let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; \
            (t1, t2)) in tlam"
           "" "(lambda (arity: 0): ... )";
         t "lambda_cyclic_tuple_apply"
           "let tlam = (lambda :let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; \
            (t1, t2)) in tlam()"
           "" "((1, (<cyclic tuple 2>, 5, 6), 3), ((1, <cyclic tuple 4>, 3), 5, 6))";
         t "given_ex_lecture_notes"
           "let foo =\n\
           \  (lambda (w, x, y, z):\n\
           \    (lambda (a):\n\
           \      let temp1 = a + x in\n\
           \      temp1 + z)) in\n\n\
            let temp2 = foo(33, 99, 55, 44) in\n\
            temp2(12)"
           "" "155";
         t "two_lambdas" "let f = (lambda (x): x + 1), g = (lambda (x): x + 2) in f(1) + g(3)" ""
           "7";
         t "lambda_mutate_tuple" "let t = (1, 2), f = (lambda : t[0] + t[1]) in (t[0] := 3; f())" ""
           "5";
         t "lecture_lam" "let f = (lambda (x): (lambda (y): x + y)) in f(3)(4)" "" "7";
         t "let_rec_nonrec" "let rec f = (lambda (x): x) in f(8)" "" "8";
         t "let_rec_nonrec_two_args" "let rec f = (lambda (x, y): x + y) in f(8, 4)" "" "12";
         t "let_rec_selfref" "let rec f = (lambda (n): if n == 1: 1 else: f(1)) in f(6)" "" "1";
         t "let_rec_fact"
           "let rec fact = (lambda (n): if n == 1: 1 else: n * fact(n - 1)) in fact(5)" "" "120";
         tvg "let_rec_fact_valgrind"
           "let rec fact = (lambda (n): if n == 1: 1 else: n * fact(n - 1)) in fact(5)" "" "120";
         t "equal_test" "let f = (lambda (e): e((1, 2, 3), (1, 2, 3))) in f(equal)" "" "true";
         t "testargs_test" "let f = (lambda (e): e(1, 2, 3, 4, 5, 6, 7, 8, 9)) in f(testarg)" ""
           "1\n2\n3\n4\n5\n6\n7\n8\n9\nfalse";
         t "piazza_test_1"
           "let x = 5 in\n\
            let y = 6 in\n\
            let z = y in\n\
            let f = (lambda: x + z) in\n\
            let h = (lambda: z + y) in\n\
            f()"
           "" "11";
         t "piazza_test_2"
           "let a = 1,\n\
           \    b = 2,\n\
           \    c = 3,\n\
           \    d = 4,\n\
           \    e = 5 in\n\
            let f = (lambda: a + e) in # only two stack slots should be allocated in f's body\n\
            f()\n"
           "" "6";
         t "let_in_lambda" "let f = (lambda (x, y): let x = x + 1, y = y + 1 in y + x) in f(4, 4)"
           "" "10";
         te "lambda_arity_low" "let f = (lambda (x, y): 4) in f(3)" "" "arity mismatch in call";
         te "lambda_arity_high" "let f = (lambda (x): 4) in f(3, 5)" "" "arity mismatch in call";
         t "let_in_lambda_inputs"
           "let f = (lambda (x, y): let x = x + input(), y = y + input() in y + x) in f(4, 4)"
           "5\n5" "18";
         t "lambda_doublecall" "let f = (lambda (x): (lambda (y): x + y)) in f(3)(4)" "" "7";
         t "lambdas_as_fvs"
           "let main = (lambda (f1, f2): f1(f2) * 2), f = (lambda (g): g(5) + 3) in main(f, \
            (lambda (x): x + 2))"
           "" "20";
         t "lambda_with_print" "let f = (lambda : print(1)) in f(); f()" "" "1\n1\n1";
         t "lambda_with_print2" "let f = (lambda (x) : print(x)) in f(1); f(2)" "" "1\n2\n2";
         t "lambda_with_input" "let f = (lambda : input()) in f() + f()" "1\n2" "3";
         t "lambda_with_input_print" "let f = (lambda : input()) in print(f)() + print(f)()" "1\n2"
           "(lambda (arity: 0): ... )\n(lambda (arity: 0): ... )\n3";
         t "letrec_in_letrec"
           "let rec f = (lambda (x): let rec g = (lambda (y): y + x) in g(x)) in f(4)" "" "8";
         t "letrec_in_letrec_call"
           "let rec f = (lambda (x): let rec h = (lambda (k): x + k) in let rec g = (lambda (y): y \
            + h(y)) in g(x)) in f(4)"
           "" "12";
         te "lambda_unary" "add1((lambda (x): x))" "" "arithmetic expected a number";
         te "lambda_binop_1" "(lambda (x): x) + 3" "" "arithmetic expected a number";
         te "lambda_binop_2" "1 + (lambda (x): x)" "" "arithmetic expected a number";
         te "lambda_binop_3" "(lambda (x): x) + (lambda (x): x)" "" "arithmetic expected a number";
         t "letrec_in_letrec_recursive"
           "let rec f = (lambda (n): let rec g = (lambda (i): if n <= 1: i else: f(i - 1) ) in \
            g(n)) in f(10)"
           "" "1";
         t "letrec_in_letrec_recursive_print"
           "let rec f = (lambda (n): let rec g = (lambda (i): if n <= 1: i else: print(f(i - 1))) \
            in g(n)) in f(10)"
           "" "1\n1\n1\n1\n1\n1\n1\n1\n1\n1";
         t "map_squared"
           "\n\n\
           \            let rec map = (lambda (f, l): if l == nil: l else: (f(l[0]), map(f, \
            l[1]))) in\n\
           \            let list = (1, (2, (3, (4, nil)))) in\n\
           \            map((lambda (x): x * x), list)\n\n\
           \            " "" "(1, (4, (9, (16, nil))))";
         t "map_print"
           "let rec map = (lambda (f, l): if l == nil: l else: (f(l[0]), map(f, l[1]))) in\n\
           \            let list = (1, (2, (3, (4, nil)))) in\n\
           \            map(print, list)\n\n\
           \            " "" "1\n2\n3\n4\n(1, (2, (3, (4, nil))))";
         t "map_print_dbg"
           "let rec map = (lambda (f, l): if l == nil: l else: (f(l[0]), map(f, l[1]))) in\n\
           \            let list = (1, (2, (3, (4, nil)))) in\n\
           \            list\n\n\
           \            " "" "(1, (2, (3, (4, nil))))";
         t "fold_sum"
           "let rec fold = (lambda (f, l, base): if l == nil: base else: f(l[0], fold(f, l[1], \
            base))) in\n\
           \            let list = (1, (2, (3, (4, nil)))) in\n\
           \            fold((lambda (n, acc): n + acc), list, 0)\n\n\
           \            " "" "10";
         t "lambda_equal_ref" "let f = (lambda (x): x) in f == f" "" "true";
         t "lambda_equal_struct_true" "let f = (lambda (x): x) in  equal(f, f)" "" "true";
         t "lambda_equal_struct_false"
           "let f = (lambda (x): x), g = (lambda (x): x) in  equal(f, g)" "" "false";
         te "call_num" "1(5)" "" "tried to call a non-closure value";
         te "call_id_not_lam" "let f = true in f(3)" "" "tried to call a non-closure value";
         t "lambda_in_tuple"
           "let t = ((lambda (x): x + 1), (lambda (x): x + 2)) in t[0](4) + t[1](4) " "" "11";
         t "lambda_tuple_args"
           "let f = (lambda ((x, y), (z, (w, p))): x + y + z + w + p), t = (1, 2) in f(t, (4, t))"
           "" "10";
         te "let_rec_nonlambda" "let rec x = 4 in x" ""
           "Let-rec expected a name binding to a lambda; got x";
         te "let_rec_nonlambda_applied" "let rec f = (lambda (x): x + 2)(3) in f(4)" ""
           "Let-rec expected a name binding to a lambda; got f";
         te "let_rec_duplicate" "let rec f = (lambda (x): x), f = (lambda (x): x) in f(4)" ""
           "The identifier f, redefined at <let_rec_duplicate, 1:29-1:30>, duplicates one at \
            <let_rec_duplicate, 1:8-1:9>";
         t "lam_in_tuple1" "((lambda (x): x), (lambda (y): y))" ""
           "((lambda (arity: 1): ... ), (lambda (arity: 1): ... ))";
         t "lam_in_tuple_access" "let t = ((lambda (x): x), (lambda (x, y): y + x)) in t[1]" ""
           "(lambda (arity: 2): ... )";
         t "lam_in_tuple_app" "let t = ((lambda (x): x), (lambda (y): y)) in t[0](4) + t[1](6)" ""
           "10";
         t "lambda_of_local_lambdas"
           "let f = (lambda : 100), g = (lambda (x): x + f()), h = (lambda (a, b): a + g(b) + f()) \
            in h(1, 2)"
           "" "203" ]

let gc_suite =
  "gc_suite"
  >::: [ tgce "oomgc1" 7 "(1, (3, 4))" "" "Out of memory";
         tgce ~no_builtins:true "oomgc1_nobuilts" 7 "(1, (3, 4))" "" "Out of memory";
         tgc "oomgc2" (16 + 8) "(1, (3, 4))" "" "(1, (3, 4))";
         tvgc "oomgc3" 28 "(1, (3, 4))" "" "(1, (3, 4))";
         tgc "oomgc4" (16 + 4) "(3, 4)" "" "(3, 4)";
         tgce "oomgc5" 3 "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation";
         tgce ~no_builtins:true "oomgc5_no_builts" 3 "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" ""
           "Allocation";
         tgc "tuple1_gc" 24 "let t = (1, 2) in let t2 = (1, t, t) in t2" "" "(1, (1, 2), (1, 2))";
         tgc "tuple1_garbage" 28
           "let t = (1, 2) in let garbage = (1, 2, 3) in let t2 = (1, t, t) in garbage; t2" ""
           "(1, (1, 2), (1, 2))";
         tgc ~no_builtins:true "tuple1_garbage_no_builts" 12
           "let t = (1, 2) in let garbage = (1, 2, 3) in let t2 = (1, t, t) in garbage; t2" ""
           "(1, (1, 2), (1, 2))";
         tgc ~no_builtins:true "tuple2_garbage_no_builts" 16
           "let t = (1, 2) in let garbage = (1, 2, 3) in let t2 = (1, t, t) in (4, 4, 4); (5, 5, \
            5); garbage; t2"
           "" "(1, (1, 2), (1, 2))";
         tgc ~no_builtins:true "tuple3_garbage_no_builts" 20
           "let t = (1, 2) in let garbage = (1, 2, 3) in let t2 = (1, t, t) in (4, 4, 4); (5, 5, \
            5); garbage; t2; (9, t2)"
           "" "(9, (1, (1, 2), (1, 2)))";
         tgc ~no_builtins:true "tuple2_letbound_gc_nobuilts" 16
           "let t = (1, 2) in t; let t = (3, 4) in t; let t = (4, 5) in t; let t = (6, 7) in t" ""
           "(6, 7)";
         tgc ~no_builtins:true "tuple2_gc_nobuilts" 4 "(1, 2); (3, 4); (4, 5); (6, 7)" "" "(6, 7)";
         tgc ~no_builtins:true "tuple2_addition_gc_nobuilts" 4
           "(1+1, 2+2); (3+3, 4+4); (4+4, 5+5); (6+6, 7+7)" "" "(12, 14)";
         tgc ~no_builtins:true "tuple2_print_gc_nobuilts_small" 8 "print((1, 2)); print((3, 4))" ""
           "(1, 2)\n(3, 4)\n(3, 4)";
         tgc ~no_builtins:true "tuple2_print_gc_nobuilts" 16
           "print((1, 2)); print((3, 4)); print((4, 5)); print((6, 7))" ""
           "(1, 2)\n(3, 4)\n(4, 5)\n(6, 7)\n(6, 7)";
         tgc "gc_lam2" (16 + 12)
           "let f = (lambda: (1, 2)) in\n       begin\n         f()\n       end" "" "(1, 2)";
         tgc "cyclic_tuple_2_gc" (16 + 12)
           "let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; (t1, t2)" ""
           "((1, (<cyclic tuple 2>, 5, 6), 3), ((1, <cyclic tuple 4>, 3), 5, 6))";
         tgc "cyclic_tuple_3_gc" (16 + 12)
           "let t1 = (1, 2, 3), t2 = (4, 5, 6) in t1[1] := t2; t2[0] := t1; (t1, t2); (t2, t1); \
            (t1, t2)"
           "" "((1, (<cyclic tuple 2>, 5, 6), 3), ((1, <cyclic tuple 4>, 3), 5, 6))";
         tgc ~no_builtins:true "gctest_given" 10 "(1, 2)" "" "(1, 2)";
         tgc ~no_builtins:true "tup_mutate_gc" 10
           "let t = (1, 2, 3) in t; (3, 4, 5, 6); t[1] := 4; (t[2], t[1], t[0], 0)" ""
           "(3, 4, 1, 0)";
         tgc "gc_lam_simple" (8 + 16) "let f = (lambda (x): x), g = (lambda (x): x) in f(3); g(5)"
           "" "5";
         tgc "gc_lam1" (10 + 16)
           "let f = (lambda: (1, 2)) in\n\
           \       begin\n\
           \         f();\n\
           \         f();\n\
           \         f();\n\
           \         f()\n\
           \       end" "" "(1, 2)";
         tgc ~no_builtins:true "gc_lam1_no_builts" 10
           "let f = (lambda: (1, 2)) in\n\
           \       begin\n\
           \         f();\n\
           \         f();\n\
           \         f();\n\
           \         f()\n\
           \       end" "" "(1, 2)";
         tgc ~no_builtins:true "gc_lam3_nobuilts" 4
           "(lambda (x): x); (lambda (x, y): x + y); (lambda (x, y, z): x + y + z)" ""
           "(lambda (arity: 3): ... )";
         tgc ~no_builtins:true "gc_lam4_nobuilts" 4
           "(lambda (x): x); (lambda (x, y): x + y); (lambda : 40)()" "" "40";
         tgc ~no_builtins:true "gc_nested_lam_copy1" 8
           "let f = (lambda (x): (lambda (y, z): x + y + z)) in print(f); print(5); f(6)" ""
           "(lambda (arity: 1): ... )\n5\n(lambda (arity: 2): ... 6 ... )";
         tgc ~no_builtins:true "gc_nested_lam_copy2_gc" 8
           "let f = (lambda (x): (lambda (y, z): x + y + z)) in print(f); print(5); (lambda (x): \
            (lambda (y, z): x + y + f(z))); f(6)"
           "" "(lambda (arity: 1): ... )\n5\n(lambda (arity: 2): ... 6 ... )";
         tgc ~no_builtins:true "gc_nested_lam_tuple_gc" 12
           "let f = (lambda (x): (lambda (y, z): x + y + z)) in print(f); print(5); (lambda (x): \
            (lambda (y, z): x + y + f(z))); f((1, 2, 3))"
           "" "(lambda (arity: 1): ... )\n5\n(lambda (arity: 2): ... (1, 2, 3) ... )";
         tgc ~no_builtins:true "gc_nested_lam_lamparam_gc" 12
           "let f = (lambda (x): (lambda (y, z): x + y + z)) in print(f); print(5); (lambda (x): \
            (lambda (y, z): x + y + f(z))); f((lambda (x): x))"
           "" "(lambda (arity: 1): ... )\n5\n(lambda (arity: 2): ... <closure fv: 0> ... )";
         tgc "gc_equals_firstclass_imm" 16 "equal;print;input;testarg" ""
           "(lambda (arity: 9): ... )";
         tgc ~no_builtins:true "gc_input_gc" 8
           "let ins = (input(), input(), input()) in (ins[0],); (ins[1], ins[2]); (ins[0], ins[1], \
            ins[2])"
           "1\n2\ntrue" "(1, 2, true)";
         tgc "gc_lam_in_tuple1" (16 + 12) "let t = ((lambda (x): x), (lambda (y): y)) in t; t" ""
           "((lambda (arity: 1): ... ), (lambda (arity: 1): ... ))";
         tgc "gc_lam_in_tuple_access" (16 + 12)
           "let t = ((lambda (x): x), (lambda (x, y): y + x)) in t[0]; t[1]" ""
           "(lambda (arity: 2): ... )";
         tgc "gc_fibonacci_tup_acc_helper" (16 + 48)
           "def fib_help(a, b, n):\n\
           \            if n == 0:\n\
           \              nil\n\
           \            else:\n\
           \              (a, fib_help(a + b, a, n - 1))\n\n\n\
           \          let fib = (lambda (n):\n\
           \           # put a + 0 to stop tail recursion on main function\n\
           \           fib_help(1, 0, n)) in fib(7);fib(5);fib(3);fib(10)\n\n\
           \           " "" "(1, (1, (2, (3, (5, (8, (13, (21, (34, (55, nil))))))))))";
         tgc "gc_lam_in_tuple_set_cyclic" (20 + 16)
           "let t = ((lambda (x): x), (lambda (y): y)) in t[0] := (lambda : t); (1, 2); (2, 3); t"
           "" "((lambda (arity: 0): ... <cyclic tuple 1> ... ), (lambda (arity: 1): ... ))";
         tgc "zero_heap_non_alloc1" 0 ~no_builtins:true "1" "" "1";
         tgc "zero_heap_non_alloc2" 0 ~no_builtins:true "true" "" "true";
         tgc "zero_heap_non_alloc3" 0 ~no_builtins:true "let x = 5 in x + 4" "" "9";
         tgc "zero_heap_non_alloc4" 0 ~no_builtins:true "nil" "" "nil";
         tgc "zero_heap_non_alloc5" 0 ~no_builtins:true "let inp = input() in if inp: 4 else: 2"
           "true" "4";
         tgc "zero_heap_non_alloc6" 0 ~no_builtins:true "let inp = input() in if inp: 4 else: 2"
           "false" "2";
         tgce "zero_heap_tuple_alloc_error" 0 ~no_builtins:true "(1, 2)" "" "Allocation error";
         tgce "zero_heap_closure_alloc_error" 0 ~no_builtins:true "(lambda : 100)" ""
           "Allocation error";
         tgce "nested_tuple_oom_error" 4 ~no_builtins:true "(1, (2, 3), 4)" "" "Out of memory";
         tgce "nested_lambda_oom_error" 4 ~no_builtins:true
           "(lambda (x): (lambda (y, z): x + y + z))(1)" "" "Out of memory";
         tgce "lambda_in_tuple_oom_error" 6 ~no_builtins:true "(1, 2, (lambda : 100), 3)" ""
           "Out of memory";
         tgc "tuple_in_lambda_no_oom" 6 ~no_builtins:true "(lambda (x, y): (x, y, 3))" ""
           "(lambda (arity: 2): ... )";
         tgce "tuple_in_lambda_oom_error" 6 ~no_builtins:true "(lambda (x, y): (x, y, 3))(1, 2)" ""
           "Out of memory";
         tgc "nested_lambda_no_oom" 4 ~no_builtins:true "(lambda (x): (lambda (y, z): x + y + z))"
           "" "(lambda (arity: 1): ... )";
         tgc "tuple_mutate_in_lambda_gc" 24
           "let t = (1, 2) in let f = (lambda : t[1] := (t[1] + 1)) in f(); f(); f(); f(); t" ""
           "(1, 6)";
         tgc "let_rec_mutate_lambda_gc" 26
           "let t = (1, 2) in let rec f = (lambda (n): if n == 0: t else: (t[0] := (t[0] + 1)); \
            f(n - 1)) in f(3)"
           "" "(4, 2)";
         tgc "lambda_of_local_lambdas" 34
           "let f = (lambda : 100), g = (lambda (x): x + f()), h = (lambda (a, b): a + g(b) + f()) \
            in h(1, 2)"
           "" "203";
         tgc ~no_builtins:true "struct_simple" 4
           "struct Posn = (x, y) in let p = new Posn(1, 2) in p" "" "(Struct <2>: (1, 2) )";
         tgc ~no_builtins:true "struct_simple_padding" 6
           "struct Posn3D = (x, y, z) in let p = new Posn3D(1, 2, 3) in p" ""
           "(Struct <2>: (1, 2, 3) )";
         tgc ~no_builtins:true "struct_with_methods" 14
           "struct Posn = (x, y) in\n\
           \          method total(): self.x + self.y\n\
           \          endstruct\n\
           \          let p = new Posn(1, 2) in p.total()" "" "3";
         tgc ~no_builtins:true "struct_with_two_methods" 22
           "struct Posn = (x, y) in\n\
           \          method total(): self.x + self.y\n\
           \           method mult(): self.x * self.y\n\
           \                     endstruct\n\
           \          let p = new Posn(1, 2) in p.mult()" "" "2";
         tgc ~no_builtins:true "struct_with_methods_with_args" 24
           "struct Posn = (x, y) in\n\
           \          method total(a): self.x + self.y + a\n\
           \           method mult(a, b): self.x * self.y * a * b\n\
           \                     endstruct\n\
           \          let p = new Posn(1, 2) in p.total(1)" "" "4";
         tgc ~no_builtins:true "struct_within_struct" 12
           "struct Cons = (first, rest : Cons) in \n\
           \           let c = new Cons(3, new Cons(2, new Cons(1, nil))) in c" ""
           "(Struct <2>: (3, (Struct <2>: (2, (Struct <2>: (1, nil) )) )) )";
         tgc ~no_builtins:true "struct_within_struct_with_methods" (18 + 24)
           "struct Cons = (first, rest : Cons) in\n\
           \           method total(): if self.rest == nil: self.first else: self.first + \
            self.rest.total()\n\
           \           endstruct\n\
           \                      let c = new Cons(3, new Cons(2, new Cons(1, nil))) in c.total()"
           "" "6" ]

let infer_suite =
  "infer_suite"
  >::: [ tinfer "no struct prog" "let x = 4 in if x == 2: true else: (x, x + 3)"
           (Program
              ( [],
                [],
                ELet
                  ( [(BName ("x_4", false, (STNone, 4)), ENumber (4L, (STNone, 5)), (STNone, 3))],
                    EIf
                      ( EPrim2 (Eq, EId ("x_4", (STNone, 8)), ENumber (2L, (STNone, 9)), (STNone, 7)),
                        EBool (true, (STNone, 10)),
                        ETuple
                          ( [ EId ("x_4", (STNone, 12));
                              EPrim2
                                ( Plus,
                                  EId ("x_4", (STNone, 14)),
                                  ENumber (3L, (STNone, 15)),
                                  (STNone, 13) ) ],
                            (STTup STNone, 11) ),
                        (STTup STNone, 6) ),
                    (STTup STNone, 2) ),
                (STTup STNone, 1) ) );
         tinfer "struct simple construct" "struct S = () in new S()"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2))],
                [],
                EConstruct ("S", [], (STSome "S", 3)),
                (STSome "S", 1) ) );
         tinfer "struct construct bound" "struct S = () in let s =  new S() in s; let g = s in g"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2))],
                [],
                ELet
                  ( [ ( BName ("s_5", false, (STSome "S", 5)),
                        EConstruct ("S", [], (STSome "S", 6)),
                        (STSome "S", 4) ) ],
                    ELet
                      ( [(BBlank (STSome "S", 9), EId ("s_5", (STSome "S", 10)), (STSome "S", 8))],
                        ELet
                          ( [ ( BName ("g_13", false, (STSome "S", 13)),
                                EId ("s_5", (STSome "S", 14)),
                                (STSome "S", 12) ) ],
                            EId ("g_13", (STSome "S", 15)),
                            (STSome "S", 11) ),
                        (STSome "S", 7) ),
                    (STSome "S", 3) ),
                (STSome "S", 1) ) );
         tinfer "struct construct bound ifs"
           "struct S = () in let s =  new S() in (if true: s else: false)"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2))],
                [],
                ELet
                  ( [ ( BName ("s_5", false, (STSome "S", 5)),
                        EConstruct ("S", [], (STSome "S", 6)),
                        (STSome "S", 4) ) ],
                    EIf
                      ( EBool (true, (STNone, 8)),
                        EId ("s_5", (STSome "S", 9)),
                        EBool (false, (STNone, 10)),
                        (STSome "S", 7) ),
                    (STSome "S", 3) ),
                (STSome "S", 1) ) );
         tinfer "struct construct lambda infer arg"
           "struct S = () in let s =  new S(), f = (lambda (x): x) in f(2); f(s); f(false)"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2))],
                [],
                ELet
                  ( [ ( BName ("s_5", false, (STSome "S", 5)),
                        EConstruct ("S", [], (STSome "S", 6)),
                        (STSome "S", 4) );
                      ( BName ("f_8", false, (STClos ([], ENil (-1), []), 8)),
                        ELambda
                          ( [BName ("x_11", false, (STNone, 11))],
                            EId ("x_11", (STNone, 10)),
                            (STClos ([], ENil (-1), []), 9) ),
                        (STClos ([], ENil (-1), []), 7) ) ],
                    ELet
                      ( [ ( BBlank (STNone, 14),
                            EApp
                              ( EId ("f_8", (STClos ([], ENil (-1), []), 17)),
                                [ENumber (2L, (STNone, 16))],
                                Snake,
                                (STNone, 15) ),
                            (STNone, 13) ) ],
                        ELet
                          ( [ ( BBlank (STSome "S", 20),
                                EApp
                                  ( EId ("f_8", (STClos ([], ENil (-1), []), 23)),
                                    [EId ("s_5", (STSome "S", 22))],
                                    Snake,
                                    (STSome "S", 21) ),
                                (STSome "S", 19) ) ],
                            EApp
                              ( EId ("f_8", (STClos ([], ENil (-1), []), 26)),
                                [EBool (false, (STNone, 25))],
                                Snake,
                                (STNone, 24) ),
                            (STNone, 18) ),
                        (STNone, 12) ),
                    (STNone, 3) ),
                (STNone, 1) ) );
         tinfer "struct construct tuple infer"
           "struct S = () in let s =  new S(), t = (s, 3, 5) in t[0]"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2))],
                [],
                ELet
                  ( [ ( BName ("s_5", false, (STSome "S", 5)),
                        EConstruct ("S", [], (STSome "S", 6)),
                        (STSome "S", 4) );
                      ( BName ("t_8", false, (STTup (STSome "S"), 8)),
                        ETuple
                          ( [ EId ("s_5", (STSome "S", 10));
                              ENumber (3L, (STNone, 11));
                              ENumber (5L, (STNone, 12)) ],
                            (STTup (STSome "S"), 9) ),
                        (STTup (STSome "S"), 7) ) ],
                    EGetItem
                      ( EId ("t_8", (STTup (STSome "S"), 15)),
                        ENumber (0L, (STNone, 14)),
                        (STSome "S", 13) ),
                    (STSome "S", 3) ),
                (STSome "S", 1) ) );
         tinfer "struct construct tuple infer cast"
           "struct S = () in struct S2 = () in let s =  new S(), s2 = new S2(), t = (s, 3, s2) in \
            (t[0] as S)"
           (Program
              ( [DStruct ("S", [], [], (STSome "S", 2)); DStruct ("S2", [], [], (STSome "S2", 3))],
                [],
                ELet
                  ( [ ( BName ("s_6", false, (STSome "S", 6)),
                        EConstruct ("S", [], (STSome "S", 7)),
                        (STSome "S", 5) );
                      ( BName ("s2_9", false, (STSome "S2", 9)),
                        EConstruct ("S2", [], (STSome "S2", 10)),
                        (STSome "S2", 8) );
                      ( BName ("t_12", false, (STTup STNone, 12)),
                        ETuple
                          ( [ EId ("s_6", (STSome "S", 14));
                              ENumber (3L, (STNone, 15));
                              EId ("s2_9", (STSome "S2", 16)) ],
                            (STTup STNone, 13) ),
                        (STTup STNone, 11) ) ],
                    EAs
                      ( EGetItem
                          ( EId ("t_12", (STTup STNone, 20)),
                            ENumber (0L, (STNone, 19)),
                            (STNone, 18) ),
                        "S",
                        (STSome "S", 17) ),
                    (STSome "S", 4) ),
                (STSome "S", 1) ) );
         tinfer "struct setters" "struct Posn = (x, y) in let p = new Posn(1, 2) in p.x := 6 "
           (Program
              ( [DStruct ("Posn", [FName "x"; FName "y"], [], (STSome "Posn", 2))],
                [],
                ELet
                  ( [ ( BName ("p_5", false, (STSome "Posn", 5)),
                        EConstruct
                          ( "Posn",
                            [ENumber (1L, (STNone, 7)); ENumber (2L, (STNone, 8))],
                            (STSome "Posn", 6) ),
                        (STSome "Posn", 4) ) ],
                    ESetter
                      ( EId ("p_5", (STSome "Posn", 11)),
                        "x",
                        ENumber (6L, (STNone, 10)),
                        (STNone, 9) ),
                    (STNone, 3) ),
                (STNone, 1) ) );
         tinfer "struct field struct"
           "struct Cons = (first, rest: Cons) in let c = new Cons(1, new Cons(2, new Cons(3, \
            nil))) in c.rest.rest"
           (Program
              ( [DStruct ("Cons", [FName "first"; FStruct ("rest", "Cons")], [], (STSome "Cons", 2))],
                [],
                ELet
                  ( [ ( BName ("c_5", false, (STSome "Cons", 5)),
                        EConstruct
                          ( "Cons",
                            [ ENumber (1L, (STNone, 7));
                              EConstruct
                                ( "Cons",
                                  [ ENumber (2L, (STNone, 9));
                                    EConstruct
                                      ( "Cons",
                                        [ENumber (3L, (STNone, 11)); ENil (STNone, 12)],
                                        (STSome "Cons", 10) ) ],
                                  (STSome "Cons", 8) ) ],
                            (STSome "Cons", 6) ),
                        (STSome "Cons", 4) ) ],
                    EGetter
                      ( EGetter (EId ("c_5", (STSome "Cons", 15)), "rest", (STSome "Cons", 14)),
                        "rest",
                        (STSome "Cons", 13) ),
                    (STSome "Cons", 3) ),
                (STSome "Cons", 1) ) );
         tinfer "struct methods"
           "struct Cons = (first, rest: Cons) in method addFirsts(c: Cons): new Cons(c.first + \
            self.first, self) endstruct let c = new Cons(1, nil) in c.addFirsts(c)"
           (Program
              ( [ DStruct
                    ( "Cons",
                      [ FName "first";
                        FStruct ("rest", "Cons");
                        FMethod
                          ( "addFirsts",
                            [BStruct ("c_27", "Cons", (STSome "Cons", 27))],
                            ELambda
                              ( [BStruct ("c_26", "Cons", (STSome "Cons", 26))],
                                ELet
                                  ( [ ( BStruct ("Cons?1_6", "Cons", (STSome "Cons", 6)),
                                        EConstruct
                                          ( "Cons",
                                            [ EPrim2
                                                ( Plus,
                                                  EGetter
                                                    ( EId ("c_26", (STSome "Cons", 10)),
                                                      "first",
                                                      (STNone, 9) ),
                                                  EGetter
                                                    ( EId ("self", (STSome "Cons", 12)),
                                                      "first",
                                                      (STNone, 11) ),
                                                  (STNone, 8) );
                                              EId ("self", (STSome "Cons", 13));
                                              EGetter
                                                ( EId ("self", (STSome "Cons", 15)),
                                                  "addFirsts",
                                                  (STNone, 14) ) ],
                                            (STSome "Cons", 7) ),
                                        (STSome "Cons", 5) ) ],
                                    ELet
                                      ( [ ( BBlank (STNone, 18),
                                            ESetter
                                              ( EAs
                                                  ( EId ("Cons?1_6", (STSome "Cons", 24)),
                                                    "Cons",
                                                    (STSome "Cons", 23) ),
                                                "addFirsts",
                                                EApp
                                                  ( EId ("tempcurry_addFirsts", (STNone, 22)),
                                                    [EId ("Cons?1_6", (STSome "Cons", 21))],
                                                    Snake,
                                                    (STNone, 20) ),
                                                (STNone, 19) ),
                                            (STNone, 17) ) ],
                                        EId ("Cons?1_6", (STSome "Cons", 25)),
                                        (STSome "Cons", 16) ),
                                    (STSome "Cons", 4) ),
                                (STClos ([], ENil (-1), []), 3) ) ) ],
                      [],
                      (STSome "Cons", 2) ) ],
                [],
                ELet
                  ( [ ( BName ("c_30", false, (STSome "Cons", 30)),
                        ELet
                          ( [ ( BStruct ("Cons?2_33", "Cons", (STSome "Cons", 33)),
                                EConstruct
                                  ( "Cons",
                                    [ ENumber (1L, (STNone, 35));
                                      ENil (STNone, 36);
                                      ENil (STNone, 37) ],
                                    (STSome "Cons", 34) ),
                                (STSome "Cons", 32) ) ],
                            ELetRec
                              ( [ ( BName
                                      ( "tempcurry_addFirsts_40",
                                        false,
                                        (STClos ([], ENil (-1), []), 40) ),
                                    ELambda
                                      ( [BStruct ("self_66", "Cons", (STSome "Cons", 66))],
                                        ELambda
                                          ( [BStruct ("c_65", "Cons", (STSome "Cons", 65))],
                                            ELet
                                              ( [ ( BStruct
                                                      ("Cons?1_45", "Cons", (STSome "Cons", 45)),
                                                    EConstruct
                                                      ( "Cons",
                                                        [ EPrim2
                                                            ( Plus,
                                                              EGetter
                                                                ( EId ("c_65", (STSome "Cons", 49)),
                                                                  "first",
                                                                  (STNone, 48) ),
                                                              EGetter
                                                                ( EId
                                                                    ("self_66", (STSome "Cons", 51)),
                                                                  "first",
                                                                  (STNone, 50) ),
                                                              (STNone, 47) );
                                                          EId ("self_66", (STSome "Cons", 52));
                                                          EGetter
                                                            ( EId ("self_66", (STSome "Cons", 54)),
                                                              "addFirsts",
                                                              (STClos ([], ENil (-1), []), 53) ) ],
                                                        (STSome "Cons", 46) ),
                                                    (STSome "Cons", 44) ) ],
                                                ELet
                                                  ( [ ( BBlank (STClos ([], ENil (-1), []), 57),
                                                        ESetter
                                                          ( EAs
                                                              ( EId
                                                                  ("Cons?1_45", (STSome "Cons", 63)),
                                                                "Cons",
                                                                (STSome "Cons", 62) ),
                                                            "addFirsts",
                                                            EApp
                                                              ( EId
                                                                  ( "tempcurry_addFirsts_40",
                                                                    (STClos ([], ENil (-1), []), 61)
                                                                  ),
                                                                [ EId
                                                                    ( "Cons?1_45",
                                                                      (STSome "Cons", 60) ) ],
                                                                Snake,
                                                                (STClos ([], ENil (-1), []), 59) ),
                                                            (STClos ([], ENil (-1), []), 58) ),
                                                        (STClos ([], ENil (-1), []), 56) ) ],
                                                    EId ("Cons?1_45", (STSome "Cons", 64)),
                                                    (STSome "Cons", 55) ),
                                                (STSome "Cons", 43) ),
                                            (STClos ([], ENil (-1), []), 42) ),
                                        (STClos ([], ENil (-1), []), 41) ),
                                    (STClos ([], ENil (-1), []), 39) ) ],
                                ESeq
                                  ( ESetter
                                      ( EAs
                                          ( EId ("Cons?2_33", (STSome "Cons", 74)),
                                            "Cons",
                                            (STSome "Cons", 73) ),
                                        "addFirsts",
                                        EApp
                                          ( EId
                                              ( "tempcurry_addFirsts_40",
                                                (STClos ([], ENil (-1), []), 72) ),
                                            [EId ("Cons?2_33", (STSome "Cons", 71))],
                                            Snake,
                                            (STClos ([], ENil (-1), []), 70) ),
                                        (STClos ([], ENil (-1), []), 69) ),
                                    EId ("Cons?2_33", (STSome "Cons", 68)),
                                    (STSome "Cons", 67) ),
                                (STSome "Cons", 38) ),
                            (STSome "Cons", 31) ),
                        (STSome "Cons", 29) ) ],
                    EApp
                      ( EGetter
                          ( EId ("c_30", (STSome "Cons", 78)),
                            "addFirsts",
                            (STClos ([], ENil (-1), []), 77) ),
                        [EId ("c_30", (STSome "Cons", 76))],
                        Snake,
                        (STSome "Cons", 75) ),
                    (STSome "Cons", 28) ),
                (STSome "Cons", 1) ) ) ]

let gensymtbl_suite =
  "gensymtbl_suite"
  >::: [ tgensym "no struct prog" "let x = 4 in if x == 2: true else: (x, x + 3)" [];
         tgensym "struct simple construct" "struct S = () in new S()"
           [(3, Either.Left {Exprs.uid= 2; field_uids= []})];
         tgensym "struct construct bound" "struct S = () in let s =  new S() in s; let g = s in g"
           [(6, Either.Left {Exprs.uid= 2; field_uids= []})];
         tgensym "struct construct bound ifs"
           "struct S = () in let s =  new S() in (if true: s else: false)"
           [(6, Either.Left {Exprs.uid= 2; field_uids= []})];
         tgensym "struct construct lambda infer arg"
           "struct S = () in let s =  new S(), f = (lambda (x): x) in f(2); f(s); f(false)"
           [(6, Either.Left {Exprs.uid= 2; field_uids= []})];
         tgensym "struct construct tuple infer"
           "struct S = () in let s =  new S(), t = (s, 3, 5) in t[0]"
           [(6, Either.Left {Exprs.uid= 2; field_uids= []})];
         tgensym "struct construct tuple infer cast"
           "struct S = () in struct S2 = () in let s =  new S(), s2 = new S2(), t = (s, 3, s2) in \
            (t[0] as S)"
           [ (7, Either.Left {Exprs.uid= 2; field_uids= []});
             (10, Either.Left {Exprs.uid= 3; field_uids= []}) ];
         tgensym "struct setters" "struct Posn = (x, y) in let p = new Posn(1, 2) in p.x := 6 "
           [ (6, Either.Left {Exprs.uid= 2; field_uids= [None; None]});
             (9, Either.Right {offset= 2; uid= 2; field_uid= None}) ];
         tgensym "struct field struct"
           "struct Cons = (first, rest: Cons) in let c = new Cons(1, new Cons(2, new Cons(3, \
            nil))) in c.rest.rest"
           [ (6, Either.Left {Exprs.uid= 2; field_uids= [None; Some 2]});
             (8, Either.Left {Exprs.uid= 2; field_uids= [None; Some 2]});
             (10, Either.Left {Exprs.uid= 2; field_uids= [None; Some 2]});
             (13, Either.Right {offset= 3; uid= 2; field_uid= Some 2});
             (14, Either.Right {offset= 3; uid= 2; field_uid= Some 2}) ];
         tgensym "struct methods"
           "struct Cons = (first, rest: Cons) in method addFirsts(c: Cons): new Cons(c.first + \
            self.first, self) endstruct let c = new Cons(1, nil) in c.addFirsts(c)"
           [ (34, Either.Left {Exprs.uid= 2; field_uids= [None; Some 2; None]});
             (46, Either.Left {Exprs.uid= 2; field_uids= [None; Some 2; None]});
             (48, Either.Right {offset= 2; uid= 2; field_uid= None});
             (50, Either.Right {offset= 2; uid= 2; field_uid= None});
             (53, Either.Right {offset= 4; uid= 2; field_uid= None});
             (58, Either.Right {offset= 4; uid= 2; field_uid= None});
             (69, Either.Right {offset= 4; uid= 2; field_uid= None});
             (77, Either.Right {offset= 4; uid= 2; field_uid= None}) ] ]

let interfere_suite =
  "interfere_suite"
  >::: [ tinterf "nothing" "1" "graph {\n}";
         tinterf "let x" "let x = 4 in x" "graph {\n  x_4\n}";
         tinterf "let xyz" "let x = 4, y = 3, z = 1 in x + y + z"
           "graph {\n\
           \  binop_13\n\
           \  x_4\n\
           \  y_7\n\
           \  z_10\n\
           \  binop_13 -- z_10\n\
           \  binop_13 -- y_7\n\
           \  binop_13 -- x_4\n\
           \  x_4 -- z_10\n\
           \  x_4 -- y_7\n\
           \  x_4 -- binop_13\n\
           \  y_7 -- z_10\n\
           \  y_7 -- x_4\n\
           \  y_7 -- binop_13\n\
           \  z_10 -- y_7\n\
           \  z_10 -- x_4\n\
           \  z_10 -- binop_13\n\
            }";
         tinterf "let xyz bind" "let x = 3, y = x + 3, z = y + x + 2 in y"
           "graph {\n\
           \  binop_14\n\
           \  x_4\n\
           \  y_7\n\
           \  z_12\n\
           \  binop_14 -- z_12\n\
           \  binop_14 -- y_7\n\
           \  binop_14 -- x_4\n\
           \  x_4 -- z_12\n\
           \  x_4 -- y_7\n\
           \  x_4 -- binop_14\n\
           \  y_7 -- z_12\n\
           \  y_7 -- x_4\n\
           \  y_7 -- binop_14\n\
           \  z_12 -- y_7\n\
           \  z_12 -- x_4\n\
           \  z_12 -- binop_14\n\
            }";
         tinterf "let in bind" "let x = (let y = x + 4 in y) in let y = (let z = x in x) in x + y "
           "graph {\n\
           \  x\n\
           \  x_4\n\
           \  y_14\n\
           \  y_7\n\
           \  z_17\n\
           \  x -- y_7\n\
           \  x_4 -- z_17\n\
           \  x_4 -- y_7\n\
           \  x_4 -- y_14\n\
           \  y_14 -- z_17\n\
           \  y_14 -- y_7\n\
           \  y_14 -- x_4\n\
           \  y_7 -- z_17\n\
           \  y_7 -- y_14\n\
           \  y_7 -- x_4\n\
           \  y_7 -- x\n\
           \  z_17 -- y_7\n\
           \  z_17 -- y_14\n\
           \  z_17 -- x_4\n\
            }";
         tinterf "if interf"
           "let x = true in if x: let y = x + 1 in y + x else: let y = x + 2 in y + x"
           "graph {\n\
           \  x_4\n\
           \  y_10\n\
           \  y_19\n\
           \  x_4 -- y_19\n\
           \  x_4 -- y_10\n\
           \  y_10 -- x_4\n\
           \  y_19 -- x_4\n\
            }";
         tinterf "let interf lambda" "let x = 1 in (lambda (a, b, c): let y = x + a in 1)"
           "graph {\n  x_4\n}";
         tinterf ~remove:(StringSet.of_list ["a"]) "(lambda (a))" "let y = x + a in x"
           "graph {\n  x\n  y_4\n  x -- y_4\n  y_4 -- x\n}";
         tinterf
           ~remove:(StringSet.of_list ["a"; "b"; "c"])
           "(lambda (a, b, c))" "let y = x + a in let x = b + c in b"
           "graph {\n  x\n  x_10\n  y_4\n  x -- y_4\n  x_10 -- y_4\n  y_4 -- x_10\n  y_4 -- x\n}";
         tinterf "let rec f lets" "let rec f = (lambda (x): x) in f(3)" "graph {\n  f_4\n}";
         tinterf "let rec f and g"
           "let rec f = (lambda (x): x) in let rec g = (lambda (k): f(k)) in g(1) + f(2)"
           "graph {\n\
           \  app_17\n\
           \  app_20\n\
           \  f_4\n\
           \  g_10\n\
           \  app_17 -- g_10\n\
           \  app_17 -- f_4\n\
           \  app_17 -- app_20\n\
           \  app_20 -- g_10\n\
           \  app_20 -- f_4\n\
           \  app_20 -- app_17\n\
           \  f_4 -- g_10\n\
           \  f_4 -- app_20\n\
           \  f_4 -- app_17\n\
           \  g_10 -- f_4\n\
           \  g_10 -- app_20\n\
           \  g_10 -- app_17\n\
            }";
         tinterf "let rec in ifs"
           "let rec f = (lambda (x): x) in if true: let rec g = (lambda (x): x) in 1 else: let rec \
            w = (lambda (x): x) in 4"
           "graph {\n\
           \  f_4\n\
           \  g_12\n\
           \  w_19\n\
           \  f_4 -- w_19\n\
           \  f_4 -- g_12\n\
           \  g_12 -- f_4\n\
           \  w_19 -- f_4\n\
            }" ]

let color_graph_suite =
  "color_graph_suite"
  >::: [ tcgraph "nothing" "1" [];
         tcgraph "let x" "let x = 4 in x" [("x_4", Reg R10)];
         tcgraph "let xyz" "let x = 4, y = 3, z = 1 in x + y + z"
           [("binop_13", Reg R10); ("x_4", Reg R12); ("y_7", Reg R13); ("z_10", Reg R14)];
         tcgraph "let xyz bind" "let x = 3, y = x + 3, z = y + x + 2 in y"
           [("binop_14", Reg R10); ("x_4", Reg R12); ("y_7", Reg R13); ("z_12", Reg R14)];
         tcgraph "let in bind" "let x = (let y = x + 4 in y) in let y = (let z = x in x) in x + y "
           [("y_7", Reg R10); ("x_4", Reg R12); ("y_14", Reg R13); ("x", Reg R12); ("z_17", Reg R14)];
         tcgraph "let interf lambda" "let x = 1 in (lambda (a, b, c): let y = x + a in 1)"
           [("x_4", Reg R10)];
         tcgraph ~remove:(StringSet.of_list ["a"]) "(lambda (a))" "let y = x + a in x"
           [("x", Reg R10); ("y_4", Reg R12)];
         tcgraph
           ~remove:(StringSet.of_list ["a"; "b"; "c"])
           "(lambda (a, b, c))" "let y = x + a in let x = b + c in b"
           [("y_4", Reg R10); ("x", Reg R12); ("x_10", Reg R12)];
         tcgraph "let rec f lets" "let rec f = (lambda (x): x) in f(3)" [("f_4", Reg R10)];
         tcgraph "let rec f and g"
           "let rec f = (lambda (x): x) in let rec g = (lambda (k): f(k)) in g(1) + f(2)"
           [("app_17", Reg R10); ("app_20", Reg R12); ("f_4", Reg R13); ("g_10", Reg R14)];
         tcgraph "let rec in ifs"
           "let rec f = (lambda (x): x) in if true: let rec g = (lambda (x): x) in 1 else: let rec \
            w = (lambda (x): x) in 4"
           [("f_4", Reg R10); ("g_12", Reg R12); ("w_19", Reg R12)] ]

let fvs_cache_suite =
  "fvs_cache_suite"
  >::: [ tfvs_cache "number" "1" (AProgram (ACExpr (CImmExpr (ImmNum (1L, ([], 1)))), ([], 0)));
         tfvs_cache "bool" "true" (AProgram (ACExpr (CImmExpr (ImmBool (true, ([], 1)))), ([], 0)));
         tfvs_cache "nil" "nil" (AProgram (ACExpr (CImmExpr (ImmNil ([], 1))), ([], 0)));
         tfvs_cache "free_id" "x"
           (AProgram (ACExpr (CImmExpr (ImmId ("x", (["x"], 1)))), (["x"], 0)));
         tfvs_cache "if_free_vars" "if a: b else: c"
           (AProgram
              ( ACExpr
                  (CIf
                     ( ImmId ("a", (["a"], 4)),
                       ACExpr (CImmExpr (ImmId ("b", (["b"], 3)))),
                       ACExpr (CImmExpr (ImmId ("c", (["c"], 2)))),
                       (["a"; "b"; "c"], 1) ) ),
                (["a"; "b"; "c"], 0) ) );
         tfvs_cache "if_no_free_vars" "if true: 100 else: 200"
           (AProgram
              ( ACExpr
                  (CIf
                     ( ImmBool (true, ([], 4)),
                       ACExpr (CImmExpr (ImmNum (100L, ([], 3)))),
                       ACExpr (CImmExpr (ImmNum (200L, ([], 2)))),
                       ([], 1) ) ),
                ([], 0) ) );
         tfvs_cache "prim1_free_vars" "add1(x)"
           (AProgram (ACExpr (CPrim1 (Add1, ImmId ("x", (["x"], 2)), (["x"], 1))), (["x"], 0)));
         tfvs_cache "prim1_free_vars_nested" "sub1((x + y))"
           (AProgram
              ( ALet
                  ( "binop_3",
                    CPrim2 (Plus, ImmId ("x", (["x"], 6)), ImmId ("y", (["y"], 5)), (["x"; "y"], 4)),
                    ACExpr (CPrim1 (Sub1, ImmId ("binop_3", (["binop_3"], 3)), (["binop_3"], 2))),
                    (["x"; "y"], 1) ),
                (["x"; "y"], 0) ) );
         tfvs_cache "prim1_no_free_vars" "add1(100)"
           (AProgram (ACExpr (CPrim1 (Add1, ImmNum (100L, ([], 2)), ([], 1))), ([], 0)));
         tfvs_cache "prim2_free_vars" "x + y"
           (AProgram
              ( ACExpr
                  (CPrim2 (Plus, ImmId ("x", (["x"], 3)), ImmId ("y", (["y"], 2)), (["x"; "y"], 1))),
                (["x"; "y"], 0) ) );
         tfvs_cache "prim2_free_vars_nested" "(a + b) - (c + d)"
           (AProgram
              ( ALet
                  ( "binop_3",
                    CPrim2
                      (Plus, ImmId ("a", (["a"], 11)), ImmId ("b", (["b"], 10)), (["a"; "b"], 9)),
                    ALet
                      ( "binop_6",
                        CPrim2
                          (Plus, ImmId ("c", (["c"], 8)), ImmId ("d", (["d"], 7)), (["c"; "d"], 6)),
                        ACExpr
                          (CPrim2
                             ( Minus,
                               ImmId ("binop_3", (["binop_3"], 5)),
                               ImmId ("binop_6", (["binop_6"], 4)),
                               (["binop_3"; "binop_6"], 3) ) ),
                        (["binop_3"; "c"; "d"], 2) ),
                    (["a"; "b"; "c"; "d"], 1) ),
                (["a"; "b"; "c"; "d"], 0) ) );
         tfvs_cache "prim2_no_free_vars" "1 + 2"
           (AProgram
              (ACExpr (CPrim2 (Plus, ImmNum (1L, ([], 3)), ImmNum (2L, ([], 2)), ([], 1))), ([], 0))
           );
         tfvs_cache "lambda_free_vars" "(lambda (x, y): x + y + k)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( ["x"; "y"],
                       ALet
                         ( "binop_4",
                           CPrim2
                             ( Plus,
                               ImmId ("x", (["x"], 8)),
                               ImmId ("y", (["y"], 7)),
                               (["x"; "y"], 6) ),
                           ACExpr
                             (CPrim2
                                ( Plus,
                                  ImmId ("binop_4", (["binop_4"], 5)),
                                  ImmId ("k", (["k"], 4)),
                                  (["binop_4"; "k"], 3) ) ),
                           (["k"; "x"; "y"], 2) ),
                       (["k"], 1) ) ),
                (["k"], 0) ) );
         tfvs_cache "lambda_only_free_vars" "(lambda : a + b)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( [],
                       ACExpr
                         (CPrim2
                            (Plus, ImmId ("a", (["a"], 4)), ImmId ("b", (["b"], 3)), (["a"; "b"], 2))
                         ),
                       (["a"; "b"], 1) ) ),
                (["a"; "b"], 0) ) );
         tfvs_cache "lambda_no_free_vars" "(lambda (x, y): x + y)"
           (AProgram
              ( ACExpr
                  (CLambda
                     ( ["x"; "y"],
                       ACExpr
                         (CPrim2
                            (Plus, ImmId ("x", (["x"], 4)), ImmId ("y", (["y"], 3)), (["x"; "y"], 2))
                         ),
                       ([], 1) ) ),
                ([], 0) ) );
         tfvs_cache "app_free_vars" "func(x, y)"
           (AProgram
              ( ACExpr
                  (CApp
                     ( ImmId ("func", (["func"], 4)),
                       [ImmId ("x", (["x"], 2)); ImmId ("y", (["y"], 3))],
                       Snake,
                       (["func"; "x"; "y"], 1) ) ),
                (["func"; "x"; "y"], 0) ) );
         tfvs_cache "app_free_vars_nested" "fun((x + y), z)"
           (AProgram
              ( ALet
                  ( "binop_3",
                    CPrim2 (Plus, ImmId ("x", (["x"], 8)), ImmId ("y", (["y"], 7)), (["x"; "y"], 6)),
                    ACExpr
                      (CApp
                         ( ImmId ("fun", (["fun"], 5)),
                           [ImmId ("binop_3", (["binop_3"], 3)); ImmId ("z", (["z"], 4))],
                           Snake,
                           (["binop_3"; "fun"; "z"], 2) ) ),
                    (["fun"; "x"; "y"; "z"], 1) ),
                (["fun"; "x"; "y"; "z"], 0) ) );
         tfvs_cache "app_no_free_vars" "fun(1, 2, 3)"
           (AProgram
              ( ACExpr
                  (CApp
                     ( ImmId ("fun", (["fun"], 5)),
                       [ImmNum (1L, ([], 2)); ImmNum (2L, ([], 3)); ImmNum (3L, ([], 4))],
                       Snake,
                       (["fun"], 1) ) ),
                (["fun"], 0) ) );
         tfvs_cache "tuple_free_vars" "(x, y, 1, 2)"
           (AProgram
              ( ACExpr
                  (CTuple
                     ( [ ImmId ("x", (["x"], 2));
                         ImmId ("y", (["y"], 3));
                         ImmNum (1L, ([], 4));
                         ImmNum (2L, ([], 5)) ],
                       (["x"; "y"], 1) ) ),
                (["x"; "y"], 0) ) );
         tfvs "tuple_free_vars_nested" "(x, y, (z), 1, 2)" ["x"; "y"; "z"];
         tfvs_cache "tuple_no_free_vars" "(1, 2, 3)"
           (AProgram
              ( ACExpr
                  (CTuple
                     ([ImmNum (1L, ([], 2)); ImmNum (2L, ([], 3)); ImmNum (3L, ([], 4))], ([], 1))
                  ),
                ([], 0) ) );
         tfvs_cache "get_free_vars" "tup[a]"
           (AProgram
              ( ACExpr
                  (CGetItem (ImmId ("tup", (["tup"], 3)), ImmId ("a", (["a"], 2)), (["a"; "tup"], 1))
                  ),
                (["a"; "tup"], 0) ) );
         tfvs_cache "get_free_vars_nested" "((1, 2, tup)[a])[b]"
           (AProgram
              ( ALet
                  ( "tup_6",
                    CTuple
                      ( [ImmNum (1L, ([], 10)); ImmNum (2L, ([], 11)); ImmId ("tup", (["tup"], 12))],
                        (["tup"], 9) ),
                    ALet
                      ( "get_4",
                        CGetItem
                          ( ImmId ("tup_6", (["tup_6"], 8)),
                            ImmId ("a", (["a"], 7)),
                            (["a"; "tup_6"], 6) ),
                        ACExpr
                          (CGetItem
                             ( ImmId ("get_4", (["get_4"], 5)),
                               ImmId ("b", (["b"], 4)),
                               (["b"; "get_4"], 3) ) ),
                        (["a"; "b"; "tup_6"], 2) ),
                    (["a"; "b"; "tup"], 1) ),
                (["a"; "b"; "tup"], 0) ) );
         tfvs_cache "get_no_free_vars" "(1, 2, 3)[2]"
           (AProgram
              ( ALet
                  ( "tup_4",
                    CTuple
                      ([ImmNum (1L, ([], 6)); ImmNum (2L, ([], 7)); ImmNum (3L, ([], 8))], ([], 5)),
                    ACExpr
                      (CGetItem
                         (ImmId ("tup_4", (["tup_4"], 4)), ImmNum (2L, ([], 3)), (["tup_4"], 2)) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvs_cache "set_free_vars" "tup[a] := b"
           (AProgram
              ( ACExpr
                  (CSetItem
                     ( ImmId ("tup", (["tup"], 4)),
                       ImmId ("a", (["a"], 3)),
                       ImmId ("b", (["b"], 2)),
                       (["a"; "b"; "tup"], 1) ) ),
                (["a"; "b"; "tup"], 0) ) );
         tfvs_cache "set_free_vars_nested" "((1, 2, tup)[a])[b] := (x + y)"
           (AProgram
              ( ALet
                  ( "tup_9",
                    CTuple
                      ( [ImmNum (1L, ([], 15)); ImmNum (2L, ([], 16)); ImmId ("tup", (["tup"], 17))],
                        (["tup"], 14) ),
                    ALet
                      ( "get_7",
                        CGetItem
                          ( ImmId ("tup_9", (["tup_9"], 13)),
                            ImmId ("a", (["a"], 12)),
                            (["a"; "tup_9"], 11) ),
                        ALet
                          ( "binop_3",
                            CPrim2
                              ( Plus,
                                ImmId ("x", (["x"], 10)),
                                ImmId ("y", (["y"], 9)),
                                (["x"; "y"], 8) ),
                            ACExpr
                              (CSetItem
                                 ( ImmId ("get_7", (["get_7"], 7)),
                                   ImmId ("b", (["b"], 6)),
                                   ImmId ("binop_3", (["binop_3"], 5)),
                                   (["b"; "binop_3"; "get_7"], 4) ) ),
                            (["b"; "get_7"; "x"; "y"], 3) ),
                        (["a"; "b"; "tup_9"; "x"; "y"], 2) ),
                    (["a"; "b"; "tup"; "x"; "y"], 1) ),
                (["a"; "b"; "tup"; "x"; "y"], 0) ) );
         tfvs_cache "set_no_free_vars" "(1, 2, 3)[2] := 100"
           (AProgram
              ( ALet
                  ( "tup_5",
                    CTuple
                      ([ImmNum (1L, ([], 7)); ImmNum (2L, ([], 8)); ImmNum (3L, ([], 9))], ([], 6)),
                    ACExpr
                      (CSetItem
                         ( ImmId ("tup_5", (["tup_5"], 5)),
                           ImmNum (2L, ([], 4)),
                           ImmNum (100L, ([], 3)),
                           (["tup_5"], 2) ) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvs_cache "let_no_free_vars" "let x = 1, y = 2 in x + y"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmNum (1L, ([], 7))),
                    ALet
                      ( "y",
                        CImmExpr (ImmNum (2L, ([], 6))),
                        ACExpr
                          (CPrim2
                             ( Plus,
                               ImmId ("x", (["x"], 5)),
                               ImmId ("y", (["y"], 4)),
                               (["x"; "y"], 3) ) ),
                        (["x"], 2) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvs_cache "let_free_vars" "let x = y, z = 10 in x + y + z + a"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmId ("y", (["y"], 15))),
                    ALet
                      ( "z",
                        CImmExpr (ImmNum (10L, ([], 14))),
                        ALet
                          ( "binop_11",
                            CPrim2
                              ( Plus,
                                ImmId ("x", (["x"], 13)),
                                ImmId ("y", (["y"], 12)),
                                (["x"; "y"], 11) ),
                            ALet
                              ( "binop_10",
                                CPrim2
                                  ( Plus,
                                    ImmId ("binop_11", (["binop_11"], 10)),
                                    ImmId ("z", (["z"], 9)),
                                    (["binop_11"; "z"], 8) ),
                                ACExpr
                                  (CPrim2
                                     ( Plus,
                                       ImmId ("binop_10", (["binop_10"], 7)),
                                       ImmId ("a", (["a"], 6)),
                                       (["a"; "binop_10"], 5) ) ),
                                (["a"; "binop_11"; "z"], 4) ),
                            (["a"; "x"; "y"; "z"], 3) ),
                        (["a"; "x"; "y"], 2) ),
                    (["a"; "y"], 1) ),
                (["a"; "y"], 0) ) );
         tfvs_cache "let_lambda_free_var" "let x = 10, y = (lambda (z): x + z) in y(100)"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmNum (10L, ([], 10))),
                    ALet
                      ( "y",
                        CLambda
                          ( ["z"],
                            ACExpr
                              (CPrim2
                                 ( Plus,
                                   ImmId ("x", (["x"], 9)),
                                   ImmId ("z", (["z"], 8)),
                                   (["x"; "z"], 7) ) ),
                            (["x"], 6) ),
                        ACExpr
                          (CApp
                             (ImmId ("y", (["y"], 5)), [ImmNum (100L, ([], 4))], Snake, (["y"], 3))
                          ),
                        (["x"], 2) ),
                    ([], 1) ),
                ([], 0) ) );
         tfvs_cache "let_rec_2" "let rec g = (lambda (y): y + h(y)) in g(x)"
           (AProgram
              ( ALetRec
                  ( [ ( "g",
                        CLambda
                          ( ["y"],
                            ALet
                              ( "app_8",
                                CApp
                                  ( ImmId ("h", (["h"], 12)),
                                    [ImmId ("y", (["y"], 11))],
                                    Snake,
                                    (["h"; "y"], 10) ),
                                ACExpr
                                  (CPrim2
                                     ( Plus,
                                       ImmId ("y", (["y"], 9)),
                                       ImmId ("app_8", (["app_8"], 8)),
                                       (["app_8"; "y"], 7) ) ),
                                (["h"; "y"], 6) ),
                            (["h"], 5) ) ) ],
                    ACExpr
                      (CApp
                         (ImmId ("g", (["g"], 4)), [ImmId ("x", (["x"], 3))], Snake, (["g"; "x"], 2))
                      ),
                    (["h"; "x"], 1) ),
                (["h"; "x"], 0) ) );
         tfvs_cache "let_rec_self_recursive" "let rec f = (lambda : f()) in f()"
           (AProgram
              ( ALetRec
                  ( [ ( "f",
                        CLambda
                          ( [],
                            ACExpr (CApp (ImmId ("f", (["f"], 6)), [], Snake, (["f"], 5))),
                            (["f"], 4) ) ) ],
                    ACExpr (CApp (ImmId ("f", (["f"], 3)), [], Snake, (["f"], 2))),
                    ([], 1) ),
                ([], 0) ) );
         tfvs_cache "sequence_free_vars" "let x = y in x; y + z"
           (AProgram
              ( ALet
                  ( "x",
                    CImmExpr (ImmId ("y", (["y"], 7))),
                    ASeq
                      ( CImmExpr (ImmId ("x", (["x"], 6))),
                        ACExpr
                          (CPrim2
                             ( Plus,
                               ImmId ("y", (["y"], 5)),
                               ImmId ("z", (["z"], 4)),
                               (["y"; "z"], 3) ) ),
                        (["x"; "y"; "z"], 2) ),
                    (["y"; "z"], 1) ),
                (["y"; "z"], 0) ) ) ]

let reg_alloc_suite =
  "reg_alloc_suite"
  >::: [ tralloc "bool" "true" [(0, [])];
         tralloc "num" "10" [(0, [])];
         tralloc "prim1" "!(false)" [(0, [])];
         tralloc "prim2_plus" "4 + 4" [(0, [])];
         tralloc "prim2_times" "4 * 3" [(0, [])];
         tralloc "true_or_false" "true || false"
           [ ( 0,
               [ ("unary_3", Reg R10);
                 ("unary_4", Reg R12);
                 ("unary_7", Reg R13);
                 ("unary_10", Reg R13) ] ) ];
         tralloc "false_and_4" "false && 4"
           [ ( 0,
               [ ("unary_3", Reg R10);
                 ("unary_4", Reg R12);
                 ("unary_7", Reg R13);
                 ("unary_10", Reg R13) ] ) ];
         tralloc "numeric_comp" "4 > 1" [(0, [])];
         tralloc "simple_let" "let x = 4 in x" [(0, [("x_4", Reg R10)])];
         tralloc "let_multiple_bindings" "let x = 4, y = 5 in x + y"
           [(0, [("x_4", Reg R10); ("y_7", Reg R12)])];
         tralloc "let_in_let_body" "let x = 4 in let y = x + 1 in y"
           [(0, [("x_4", Reg R10); ("y_8", Reg R12)])];
         tralloc "let_in_let_binding" "let x = 5, y = (let x = 3 in x) in y"
           [(0, [("x_4", Reg R12); ("x_10", Reg R10); ("y_7", Reg R13)])];
         tralloc "nested_lets" "let x = 2 in let y = x in let z = y in z"
           [(0, [("x_4", Reg R10); ("y_8", Reg R12); ("z_12", Reg R13)])];
         tralloc "lets_nested_binding_and_body" "let y = 2, x = (let x = 3 in x) in let z = x in z"
           [(0, [("y_4", Reg R13); ("x_10", Reg R10); ("x_7", Reg R12); ("z_15", Reg R14)])];
         tralloc "if_in_let_body" "let x = true, y = 10, z = 5 in (if x: y else: z)"
           [(0, [("x_4", Reg R10); ("y_7", Reg R12); ("z_10", Reg R13)])];
         tralloc "if_in_let_binding" "let x = (if true: 3 else: 5) in x + 4"
           [(0, [("x_4", Reg R10)])];
         tralloc "function_def_one_arg" "def f(x): x\n\nf(5)"
           [(0, [("f_4", Reg R10)]); (5, [("x_7", RegOffset (24, RBP))])];
         tralloc "function_def_multiple_args" "def f(x, y): x + y\n\nf(5, 3)"
           [ (0, [("f_4", Reg R10)]);
             (6, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tralloc "multiple_function_defs_with_let_inside_def"
           "def f(x, y): x + y\ndef g(x, y, z): let h = 4 in h\n\nh()"
           [ (0, [("f_4", Reg R10); ("g_13", Reg R12)]);
             ( 5,
               [ ("h_17", Reg R10);
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (9, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tralloc "multiple_function_defs_with_let_inside_def_and_body"
           "def f(x, y): x + y\ndef g(x, y, z): let h = 4 in h\n\nlet x = 5 in f(x, x)"
           [ (0, [("f_4", Reg R10); ("g_13", Reg R12); ("x_25", Reg R13)]);
             ( 9,
               [ ("h_17", Reg R10);
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP));
                 ("z_22", RegOffset (40, RBP)) ] );
             (13, [("x_9", RegOffset (24, RBP)); ("y_10", RegOffset (32, RBP))]) ];
         tralloc "def_with_if_inside"
           "def f(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\nf(1, 2)"
           [ (0, [("f_4", Reg R10)]);
             ( 6,
               [ ("g_10", Reg R10);
                 ("h_15", Reg R10);
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         tralloc "def_with_let_multiple_bindings"
           "def f(x, y, z): let g = 1 in let z = 5 in g\n\nlet x = 5 in x"
           [ (0, [("f_4", Reg R10); ("x_20", Reg R12)]);
             ( 5,
               [ ("g_8", Reg R10);
                 ("z_12", Reg R12);
                 ("x_15", RegOffset (24, RBP));
                 ("y_16", RegOffset (32, RBP));
                 ("z_17", RegOffset (40, RBP)) ] ) ];
         tralloc "complex_1"
           "def f(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\
            def g(x, y): if x: (let g = 4 in g) else: (let h = 4 in h)\n\n\
            let x = 1, y = 2 in f(x, y) + g(x, y)"
           [ ( 0,
               [ ("app_46", Reg R10);
                 ("app_50", Reg R12);
                 ("f_4", Reg R13);
                 ("g_22", Reg R14);
                 ("x_40", Reg RBX);
                 ("y_43", Reg RDI) ] );
             ( 20,
               [ ("g_28", Reg R10);
                 ("h_33", Reg R10);
                 ("x_36", RegOffset (24, RBP));
                 ("y_37", RegOffset (32, RBP)) ] );
             ( 29,
               [ ("g_10", Reg R10);
                 ("h_15", Reg R10);
                 ("x_18", RegOffset (24, RBP));
                 ("y_19", RegOffset (32, RBP)) ] ) ];
         tralloc "tup_creation" "let t = (1, 2, 3) in t" [(0, [("t_4", Reg R10)])];
         tralloc "multiple_tup_creation" "let t = (1, 2, 3), y = (3, 4, 5) in y"
           [(0, [("t_4", Reg R10); ("y_10", Reg R12)])];
         tralloc "tup_destruct" "let t = (1, 2, 3), a = t[0], b = t[1], c = t[2] in c"
           [(0, [("a_10", Reg R10); ("b_15", Reg R12); ("c_20", Reg R13); ("t_4", Reg R14)])];
         tralloc "tup_creation_def" "def f(x): ((x + 1), (x - 1))\n\nf(4)"
           [ (0, [("f_4", Reg R10)]);
             (5, [("binop_7", Reg R12); ("binop_10", Reg R10); ("x_13", RegOffset (24, RBP))]) ];
         tralloc "tup_def_destruct"
           "def f(x): let t = ((x + 1), (x - 1)), b = t[0], c = t[1] in b + c\n\nf(4)"
           [ (0, [("f_4", Reg R10)]);
             ( 5,
               [ ("b_17", Reg R10);
                 ("binop_10", Reg R12);
                 ("binop_13", Reg R13);
                 ("c_22", Reg R14);
                 ("t_8", Reg RBX);
                 ("x_29", RegOffset (24, RBP)) ] ) ];
         tralloc "tup_def_destruct_in_prog_body"
           "def f(x): let t = ((x + 1), (x - 1)), b = t[0], c = t[1] in b + c\n\n\
            let t = (1, 2), x = t[0], y = t[1] in f(x + y)"
           [ ( 0,
               [ ("binop_47", Reg R10);
                 ("f_4", Reg R12);
                 ("t_32", Reg R13);
                 ("x_37", Reg R14);
                 ("y_42", Reg RBX) ] );
             ( 21,
               [ ("b_17", Reg R10);
                 ("binop_10", Reg R12);
                 ("binop_13", Reg R13);
                 ("c_22", Reg R14);
                 ("t_8", Reg RBX);
                 ("x_29", RegOffset (24, RBP)) ] ) ];
         tralloc "tup_destruct_in_func_args"
           "def f((a, b), (c, d)): a + b + c + d\n\nlet t1 = (1, 2), t2 = (3, 4) in f(t1, t2)"
           [ (0, [("f_4", Reg R10); ("t1_54", Reg R12); ("t2_59", Reg R13)]);
             ( 14,
               [ ("a_16", Reg R10);
                 ("arg_tup?2_50", RegOffset (24, RBP));
                 ("arg_tup?1_51", RegOffset (32, RBP));
                 ("b_21", Reg R12);
                 ("binop_45", Reg R14);
                 ("binop_44", Reg R13);
                 ("c_34", Reg RBX);
                 ("d_39", Reg RDI);
                 ("tup?3_8", Reg RSI);
                 ("tup?4_26", Reg RDX) ] ) ];
         tralloc "blank_in_def" "def f(x, _, _): x\n\nf(5, 1, 2)"
           [ (0, [("f_4", Reg R10)]);
             ( 7,
               [ ("x_7", RegOffset (24, RBP));
                 ("__8", RegOffset (32, RBP));
                 ("__9", RegOffset (40, RBP)) ] ) ];
         tralloc "blank_in_def_tup" "def f(x, (y, _), _): x + y\n\nf(1, (2, 3), 4)"
           [ (0, [("f_4", Reg R10); ("tup_33", Reg R12)]);
             ( 11,
               [ ("arg_tup?1_29", RegOffset (32, RBP));
                 ("tup?2_8", Reg R10);
                 ("y_16", Reg R12);
                 ("x_28", RegOffset (24, RBP));
                 ("__30", RegOffset (40, RBP)) ] ) ];
         tralloc "sequence" "let x = 4 in x; let y = 4 in y"
           [(0, [("x_4", Reg R10); ("y_12", Reg R12)])];
         tralloc "sequence_with_lets"
           "let x = 4, y = 5, z = 10 in x + y + z; let a = 1, b = 2, c = 3 in a + b + c"
           [ ( 0,
               [ ("x_4", Reg RDI);
                 ("y_7", Reg RSI);
                 ("z_10", Reg RDX);
                 ("binop_16", Reg R13);
                 ("a_22", Reg R10);
                 ("b_25", Reg R12);
                 ("c_28", Reg RBX);
                 ("binop_31", Reg R14) ] ) ];
         tralloc "lambda_lit_one_arg_simple" "(lambda (x): x)"
           [(0, []); (1, [("x_4", RegOffset (24, RBP))])];
         tralloc "lambda_lit_fv" "let y = 3 in (lambda (x): x + y)"
           [(0, [("y_4", Reg R10)]); (2, [("x_10", RegOffset (24, RBP)); ("y_4", Reg R10)])];
         tralloc "lambda_empty_lit" "(lambda : 1)" [(0, []); (1, [])];
         tralloc "two_lambdas" "let f = (lambda (x): x + 1), g = (lambda (x): x + 2) in f(1) + g(3)"
           [ (0, [("f_4", Reg R13); ("g_11", Reg R14); ("app_18", Reg R10); ("app_21", Reg R12)]);
             (14, [("x_16", RegOffset (24, RBP))]);
             (18, [("x_9", RegOffset (24, RBP))]) ];
         tralloc "let_in_lambda"
           "let f = (lambda (x, y): let x = x + 1, y = y + 1 in y + x) in f(4, 4)"
           [ (0, [("f_4", Reg R10)]);
             ( 6,
               [ ("x_8", Reg R10);
                 ("y_13", Reg R12);
                 ("x_20", RegOffset (24, RBP));
                 ("y_21", RegOffset (32, RBP)) ] ) ];
         tralloc "lambda_in_lambda_fv" "(lambda (x): (lambda (y): y + x)(5))(4)"
           [ (0, [("lam_4", Reg R10)]);
             (5, [("lam_7", Reg R10); ("x_12", RegOffset (24, RBP))]);
             (10, [("y_11", RegOffset (24, RBP)); ("x_12", Reg R10)]) ];
         tralloc "letrec_in_letrec_recursive"
           "let rec f = (lambda (n): let rec g = (lambda (i): if n <= 1: i else: f(i - 1) ) in \
            g(n)) in f(10)"
           [ (0, [("f_4", Reg R10)]);
             (5, [("g_8", Reg R12); ("n_24", RegOffset (24, RBP)); ("f_4", Reg R10)]);
             ( 10,
               [ ("binop_11", Reg R10);
                 ("binop_16", Reg R12);
                 ("i_20", RegOffset (24, RBP));
                 ("f_4", Reg R13);
                 ("n_24", Reg R14) ] ) ] ]

let struct_suite =
  "struct_suite"
  >::: [ t "struct_simple" "struct Posn = (x, y) in new Posn(1, 2)" "" "(Struct <2>: (1, 2) )";
         t "struct_let_bound" "struct Posn = (x, y) in let p = new Posn(1, 2) in p" ""
           "(Struct <2>: (1, 2) )";
         t "struct_tuple" "struct Posn = (x, y) in let p = new Posn(1, 2) in (p, p, p)" ""
           "((Struct <2>: (1, 2) ), (Struct <2>: (1, 2) ), (Struct <2>: (1, 2) ))";
         t "struct_in_struct"
           "struct Posn = (x, y) in struct Pair = (l: Posn, r: Posn) in let pos1 = new Posn(5, 9), \
            pos2 = new Posn(3, 7) in new Pair(pos1, pos2)"
           "" "(Struct <3>: ((Struct <2>: (5, 9) ), (Struct <2>: (3, 7) )) )";
         t "struct_lambda_ret_posn"
           "struct Posn = (x, y) in let f = (lambda (x, y): new Posn(x, y)) in f(1, 2)" ""
           "(Struct <2>: (1, 2) )";
         t "struct_lambda_args"
           "struct Posn = (x, y) in struct Pair = (l: Posn, r: Posn) in let pos1 = new Posn(1, 2), \
            pos2 = new Posn(2, 3) in let f = (lambda (p1, p2): new Pair(p1, p2)) in f(pos1, pos2)"
           "" "(Struct <3>: ((Struct <2>: (1, 2) ), (Struct <2>: (2, 3) )) )";
         t "is_posn3d_true"
           "struct Posn3D = (x, y, z) in let p = new Posn3D(1, 2, 3) in (p is Posn3D)" "" "true";
         t "is_posn3d_false"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in let p = new Posn(1, 2) in (p is \
            Posn3D)"
           "" "false";
         t "is_posn_true"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in let p = new Posn(1, 2) in (p is \
            Posn)"
           "" "true";
         t "is_posn_false"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in let p = new Posn3D(1, 2, 3) in (p \
            is Posn)"
           "" "false";
         te "tuple_boolstuff" "!((1, 2, 3))" "" "logic expected a boolean";
         te "posn_boolstuff"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in let p = new Posn3D(1, 2, 3) in \
            !(p)"
           "" "logic expected a boolean";
         t "bool_is_struct"
           "struct Posn = (x, y) in struct Posn3D = (x, y, z) in let p = new Posn3D(1, 2, 3) in \
            (true is Posn3D)"
           "" "false";
         t "get_posn_x" "struct Posn = (x, y) in new Posn(1, 2).x" "" "1";
         t "get_posn_y" "struct Posn = (x, y) in new Posn(1, 2).y" "" "2";
         te "get_posn_z" "struct Posn = (x, y) in new Posn(1, 2).z" ""
           "a getter couldn't find the field. got offset";
         t "get_posn3d_z" "struct Posn3D = (x, y, z) in new Posn3D(1, 2, 3).z" "" "3";
         t "get_posn_x_letbound" "struct Posn = (x, y) in let p = new Posn(1, 2) in p.x + p.y" ""
           "3";
         t "is_tuple" "struct Posn = (x, y) in ((1, 2, 3) is Posn)" "" "false";
         t "istuple_struct" "struct Posn = (x, y) in let p = new Posn(1, 2) in istuple(p)" ""
           "false";
         te "tuple_getter_on_struct1"
           "struct Struct = (a, b, c, d) in let p = new Struct(1, 2, 3, 4) in p[3]" ""
           "get expected tuple";
         te "tuple_get_on_struct2"
           "struct Struct = (a, b, c, d, e) in let p = new Struct(1, 2, 3, 4, 5) in p[4]" ""
           "get expected tuple";
         te "tuple_set_on_struct1"
           "struct Struct = (a, b, c, d, e) in let p = new Struct(1, 2, 3, 4, 5) in p[0] := 5; \
            p[1] := 4; p[2] := 3; p[3] := 2; p[4] := 1; p"
           "" "set expected tuple";
         te "tuple_destruct_struct"
           "struct Posn = (x, y) in let p = new Posn(1, 2) in let (x, y) = p in x + y" ""
           "a tuple was badly destructed";
         te "tuple_destruct_struct_bad"
           "struct Posn = (x, y) in let p = new Posn(1, 2) in let (x, y, z) = p in x + y" ""
           "a tuple was badly destructed";
         t "posn_equal_posn_true"
           "struct Posn = (x, y) in let p1 = new Posn(1, 2), p2 = new Posn(1, 2) in equal(p1, p2)"
           "" "true";
         t "posn_equal_posn_false"
           "struct Posn = (x, y) in let p1 = new Posn(1, 2), p2 = new Posn(3, 2) in equal(p1, p2)"
           "" "false";
         t "posn_equal_diff_posn_false"
           "struct Posn1 = (x, y) in struct Posn2 = (x, y) in let p1 = new Posn1(1, 2), p2 = new \
            Posn2(1, 2) in equal(p1, p2)"
           "" "false";
         t "posn_equal_diff_posn3d_false"
           "struct Posn1 = (x, y) in struct Posn3D = (x, y, z) in let p1 = new Posn1(1, 2), p2 = \
            new Posn3D(1, 2, 3) in print(p1); print(p2); equal(p1, p2)"
           "" "(Struct <2>: (1, 2) )\n(Struct <3>: (1, 2, 3) )\nfalse";
         t "posn_set_both"
           "struct Posn = (x, y) in let p = new Posn(1, 2) in print(p.x := 4);print(p.y := 6); p" ""
           "4\n6\n(Struct <2>: (4, 6) )";
         t "method_manual_creation_var"
           "struct Posn = (x, y, addUp) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_var = 4 in\n\
           \                        temp_p.addUp := temp_var; temp_p ) in p" ""
           "(Struct <2>: (3, 2, 4) )";
         t "method_manual_creation_retlam"
           "struct Posn = (x, y, addUp) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_lam = (lambda : let this: Posn = temp_p in this.x + this.y) in\n\
           \                        temp_lam ) in p" ""
           "(lambda (arity: 0): ... <struct fv: 0> ... )";
         t "method_manual_creation"
           "struct Posn = (x, y, addUp) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_lam = (lambda : let this: Posn = temp_p in this.x + this.y) in\n\
           \                        temp_p.addUp := temp_lam; temp_p ) in p" ""
           "(Struct <2>: (3, 2, <closure field: 2>) )";
         t "method_manual_creation_access_lam"
           "struct Posn = (x, y, addUp) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_lam = (lambda : let this: Posn = temp_p in this.x + this.y) in\n\
           \                        temp_p.addUp := temp_lam; temp_p ) in p.addUp" ""
           "(lambda (arity: 0): ... <struct fv: 0> ... )";
         t "method_manual_creation_apply"
           "struct Posn = (x, y, addUp) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_lam = (lambda : let this: Posn = temp_p in this.x + this.y) in\n\
           \                        temp_p.addUp := temp_lam; temp_p ) in p.addUp()" "" "5";
         t "method_recursive_manual"
           "struct Posn = (x, y, addUpTillZero) in \n\
           \             let p = (let temp_p = new Posn(3, 2, nil) in\n\
           \             let temp_lam = (lambda (n): let this: Posn = temp_p in \n\
           \             if (n == 0): 0 else: this.x + this.y + this.addUpTillZero(n - 1)) in\n\
           \                        temp_p.addUpTillZero := temp_lam; temp_p ) in \
            p.addUpTillZero(4)"
           "" "20";
         t "method_recursive_retself_manual"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let temp_lam = (lambda (n): let this: Cons = temp_p in \n\
           \             if (n == 0): nil else: new Cons(n, this.genCons(n - 1), this.genCons)) in\n\
           \             temp_p.genCons := temp_lam; temp_p ) in c.genCons(4)" ""
           "(Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, (Struct <2>: (1, nil, <closure \
            field: 2>) ), <closure field: 2>) ), <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_retself_manual_dependant"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let temp_lam = (lambda (n): let this: Cons = temp_p in \n\
           \             if (n == 0): nil else: new Cons(n + this.first, this.genCons(n - 1), \
            this.genCons)) in\n\
           \             temp_p.genCons := temp_lam; temp_p ) in (c.genCons(4) as Cons).genCons(3)"
           ""
           "(Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, nil, <closure field: 2>) ), \
            <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_retself_manual_dependant_works"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let rec temp_lam = (lambda (this : Cons): (lambda (n): \n\
           \             if (n == 0): nil else: let temp_c = new Cons(n + this.first, \
            this.genCons(n - 1), nil)\n\
           \             in temp_c.genCons := temp_lam(temp_c); temp_c)) in\n\
           \             temp_p.genCons := temp_lam(temp_p); temp_p ) in (c.genCons(3) as \
            Cons).genCons(3)"
           ""
           "(Struct <2>: (7, (Struct <2>: (6, (Struct <2>: (5, nil, <closure field: 2>) ), \
            <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_retself_manual_dependant_boxed"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c: Cons = (let temp_p = (new Cons(1, nil, nil),) in\n\
           \             let temp_lam = (lambda (n): let this: Cons = temp_p[0] in \n\
           \             if (n == 0): nil else: new Cons(n + this.first, this.genCons(n - 1), \
            this.genCons)) in\n\
           \             temp_p[0].genCons := temp_lam; temp_p[0] ) in (c.genCons(4) as \
            Cons).genCons(3)"
           ""
           "(Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, nil, <closure field: 2>) ), \
            <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_retself_manual_dependant_letrec"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let rec temp_lam = (lambda (n): let this: Cons = temp_p in \n\
           \             if (n == 0): nil else: new Cons(n + this.first, temp_lam(n - 1), \
            temp_lam)) in\n\
           \             temp_p.genCons := temp_lam; temp_p ) in (c.genCons(4) as Cons).genCons(3)"
           ""
           "(Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, nil, <closure field: 2>) ), \
            <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_retself_manual_nosetter"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let rec temp_p = (lambda : new Cons(1, nil, (lambda (n): let \
            this: Cons = temp_p() in if (n == 0): nil else: new Cons(n, this.genCons(n - 1), \
            this.genCons))))\n\
           \              in\n\
           \             (temp_p() as Cons )) in c.genCons(4)" ""
           "(Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, (Struct <2>: (1, nil, <closure \
            field: 2>) ), <closure field: 2>) ), <closure field: 2>) ), <closure field: 2>) )";
         t "method_recursive_foldr"
           "struct Cons = (first, rest: Cons, foldr) in \n\
           \             let c: Cons = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let temp_fold = (lambda (f, base): let this: Cons = temp_p in\n\
           \             if (this.rest == nil): f(this.first, base) else: f(this.first, \
            this.rest.foldr(f, base)) ) in\n\
           \             temp_p.foldr := temp_fold; temp_p ) in c.foldr((lambda (i, acc): i + \
            acc), 0)"
           "" "1";
         t "method_recursive_foldr_and_gencons_nonsetter"
           "struct Cons = (first, rest: Cons, genCons, foldr) in \n\
           \             let c: Cons = (let rec temp_p = (lambda : new Cons(1, nil, (lambda (n): \
            let this: Cons = temp_p() in if (n == 0): nil else: new Cons(n, this.genCons(n - 1), \
            (temp_p() as Cons).genCons, (temp_p() as Cons).foldr)), (lambda (f, base): let this: \
            Cons = temp_p() in if (this.rest == nil): print(this); f(this.first, base) else: \
            print(f(this.first, this.rest.foldr(f, base)) )))) in\n\
           \             temp_p() ) in (c.genCons(3) as Cons).foldr" ""
           "(lambda (arity: 2): ... <closure fv: 0> ... )";
         t "method_recursive_retself_manual_as_access"
           "struct Cons = (first, rest: Cons, genCons) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil) in\n\
           \             let temp_lam = (lambda (n): let this: Cons = temp_p in \n\
           \             if (n == 0): nil else: new Cons(n, this.genCons(n - 1), this.genCons)) in\n\
           \             temp_p.genCons := temp_lam; temp_p ) in (c.genCons(4) as \
            Cons).rest.rest.rest.first"
           "" "1";
         t "method_recursive_retself_foldr_gencons_bad"
           "struct Cons = (first, rest: Cons, genCons, foldr) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil, nil) in\n\
           \             let rec temp_gcons = (lambda (this : Cons): (lambda (n): \n\
           \             if (n == 0): nil else: let temp_c = new Cons(n, this.genCons(n - 1), \
            this.genCons, this.foldr)\n\
           \             in temp_c.genCons := temp_gcons(temp_c); temp_c)) in\n\
           \             let rec temp_fold = (lambda (this : Cons): (lambda (f, base): if \
            (print(this.rest) == nil):\n\
           \             f(this.first, base) else: this.rest.foldr(f, f(this.first, base)))) in\n\
           \             temp_p.foldr := temp_fold(temp_p);\n\
           \             temp_p.genCons := temp_gcons(temp_p); temp_p ) in (c.genCons(3) as \
            Cons).foldr((lambda (i, acc): i + acc), 0)"
           "" "nil\n1";
         (* NOTE: so the trick is that every time we recreate a new struct (of the self type) inside of a method, *)
         (*       we have to also patch the functions from self by calling the curried lambda *)
         t "method_recursive_retself_foldr_gencons_works"
           "struct Cons = (first, rest: Cons, genCons, foldr) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil, nil) in\n\
           \             let rec temp_fold = (lambda (this : Cons): (lambda (f, base): if \
            (this.rest == nil):\n\
           \             f(this.first, base) else: this.rest.foldr(f, f(this.first, base)))) in\n\
           \             let rec temp_gcons = (lambda (this : Cons): (lambda (n): \n\
           \             if (n == 0): nil else: let temp_c = new Cons(n, this.genCons(n - 1), \
            this.genCons, this.foldr)\n\
           \             in temp_c.genCons := temp_gcons(temp_c); temp_c.foldr := \
            temp_fold(temp_c); temp_c)) in\n\
           \             temp_p.foldr := temp_fold(temp_p);\n\
           \             temp_p.genCons := temp_gcons(temp_p); temp_p ) in (c.genCons(3) as \
            Cons).foldr((lambda (i, acc): i + acc), 0)"
           "" "6";
         t "method_recursive_retself_foldr_gencons_mutual_rec"
           "struct Cons = (first, rest: Cons, genCons, foldr) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil, nil) in\n\
           \             let rec temp_gcons = (lambda (this : Cons): (lambda (n): \n\
           \             if (n == 0): nil else: let temp_c = new Cons(n, this.genCons(n - 1), \
            this.genCons, this.foldr)\n\
           \             in temp_c.genCons := temp_gcons(temp_c); temp_c.foldr := \
            temp_fold(temp_c); temp_c)), \n\
           \             temp_fold = (lambda (this : Cons): (lambda (f, base): if (this.rest == \
            nil):\n\
           \             f(this.first, base) else: this.rest.foldr(f, f(this.first, base)))) in\n\
           \             temp_p.foldr := temp_fold(temp_p);\n\
           \             temp_p.genCons := temp_gcons(temp_p); temp_p ) in (c.genCons(3) as \
            Cons).foldr((lambda (i, acc): i + acc), 0)"
           "" "6";
         t "method_recursive_retself_foldr_gencons_map_mutual_rec"
           "struct Cons = (first, rest: Cons, genCons, foldr, map) in \n\
           \             let c = (let temp_p = new Cons(1, nil, nil, nil, nil) in\n\
           \             let rec temp_gcons = (lambda (this : Cons): (lambda (n): \n\
           \             if (n == 0): nil else: let temp_c = new Cons(n, this.genCons(n - 1), \
            this.genCons, this.foldr, this.map)\n\
           \             in temp_c.genCons := temp_gcons(temp_c); temp_c.foldr := \
            temp_fold(temp_c); temp_c.map := temp_map(temp_c); temp_c)), \n\
           \             temp_fold = (lambda (this : Cons): (lambda (f, base): if (this.rest == \
            nil):\n\
           \             f(this.first, base) else: this.rest.foldr(f, f(this.first, base)))),\n\
           \             temp_map = (lambda (this : Cons): (lambda (f): if (this.rest == nil): let \
            temp_els = new Cons(f(this.first), nil, this.genCons, this.foldr, this.map) in  \
            temp_els.genCons := temp_gcons(temp_els); temp_els.foldr := temp_fold(temp_els); \
            temp_els.map := temp_map(temp_els); temp_els\n\
           \             else: let temp_res = new Cons(f(this.first), this.rest.map(f), \
            this.genCons, this.foldr, this.map) in\n\
           \             temp_res.genCons := temp_gcons(temp_res); temp_res.foldr := \
            temp_fold(temp_res); temp_res.map := temp_map(temp_res); temp_res)) in\n\
           \                        temp_p.foldr := temp_fold(temp_p);\n\
           \             temp_p.map := temp_map(temp_p);\n\
           \             temp_p.genCons := temp_gcons(temp_p); temp_p ) in ((c.genCons(3) as \
            Cons).map((lambda (i): i * 10)) as Cons).foldr((lambda (i, acc): i + acc), 0)"
           "" "60";
         t "closure_in_struct_with_fv"
           "struct Posn = (x, y, f) in let tup = (0, 1), f = (lambda : tup[0] := tup[0] + 1) in\n\
           \        let p = new Posn(10, 20, f) in p.f(); p.f(); p.f(); tup" "" "(3, 1)";
         tgc "struct_garbage" 20
           "struct Posn = (x, y) in new Posn(6, 2); new Posn(5, 2); new Posn(2, 3)" ""
           "(Struct <2>: (2, 3) )";
         tgc "struct_copy" 28
           "struct Cons = (first, rest: Cons) in let l1 = new Cons(1, nil), l2 = new Cons(2, l1), \
            l3 = new Cons(3, l2) in l3"
           "" "(Struct <2>: (3, (Struct <2>: (2, (Struct <2>: (1, nil) )) )) )";
         t "posn_method"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct let p = new Posn(1, \
            2) in p.addUp"
           "" "(lambda (arity: 0): ... <struct fv: 0> ... )";
         t "posn_method_apply"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct let p = new Posn(1, \
            2) in p.addUp()"
           "" "3";
         t "cons_gencons"
           "struct Cons = (first, rest: Cons) in \n\
           \ method genCons(n): if (n == 0): nil else: new Cons(n, self.genCons(n - 1))\n\
           \ endstruct\n\
           \ let c = new Cons(1, nil) in c.genCons(5)" ""
           "(Struct <2>: (5, (Struct <2>: (4, (Struct <2>: (3, (Struct <2>: (2, (Struct <2>: (1, \
            nil, <closure field: 2>) ), <closure field: 2>) ), <closure field: 2>) ), <closure \
            field: 2>) ), <closure field: 2>) )";
         t "cons_gencons_foldr"
           "struct Cons = (first, rest: Cons) in \n\
           \ method genCons(n): if (n == 0): nil else: new Cons(n, self.genCons(n - 1))\n\
           \ method foldr(f, base): if (self.rest == nil): f(self.first, base) else: f(self.first, \
            self.rest.foldr(f, base))\n\
           \ endstruct\n\
           \ let c = new Cons(1, nil) in c.genCons(5).foldr((lambda (i, acc): i + acc), 0)" "" "15";
         t "cons_gencons_foldr_foldl"
           "struct Cons = (first, rest: Cons) in \n\
           \ method genCons(n): if (n == 0): nil else: new Cons(n, self.genCons(n - 1))\n\
           \ method foldr(f, base): if (self.rest == nil): f(self.first, base) else: f(self.first, \
            self.rest.foldr(f, base))\n\
           \ method foldl(f, base): if (self.rest == nil): f(self.first, base) else: \
            self.rest.foldl(f, f(self.first, base))\n\
           \ method map(f): if (self.rest == nil): new Cons(f(self.first), nil) else: new \
            Cons(f(self.first), self.rest.map(f))\n\
           \ endstruct\n\
           \ let c = new Cons(1, nil) in\n\
           \ let conses = c.genCons(5), sum = conses.foldr((lambda (i, acc): i + acc), 0) in\n\
           \ let tuplefiedLeft = conses.map((lambda (i): i * 2)).foldl((lambda (i, acc): (i, \
            acc)), sum) in\n\
           \ let tuplefiedRight = conses.map((lambda (i): i * 2)).foldr((lambda (i, acc): (i, \
            acc)), sum) in\n\
           \ (tuplefiedLeft, tuplefiedRight)" ""
           "((2, (4, (6, (8, (10, 15))))), (10, (8, (6, (4, (2, 15))))))";
         t "method_param_mutate"
           "struct Posn = (x, y) in \n\
           \ method incrX(): self.x := self.x + 1\n\
           \ method incrY(): self.y := self.y + 1\n\
           \ endstruct\n\
           \ let p = new Posn(1, 2) in p.incrX(); p.incrX(); p.incrY(); p.incrX(); p.incrY(); p" ""
           "(Struct <2>: (4, 4, <closure field: 2>, <closure field: 3>) )";
         t "closed_over_method1"
           "struct Posn = (x, y) in \n\
           \ method getX(): self.x\n\
           \ method getY(): self.y\n\
           \ endstruct\n\
           \ let p = new Posn(1, 2), close = p.getX in\n\
           \ p.x := 999; (p.getX(), close(), p.getY())" "" "(999, 999, 2)";
         t "closed_over_method2"
           "struct Posn = (x, y) in \n\
           \ method incrX(): self.x := self.x + 1\n\
           \ method incrY(): self.y := self.y + 1\n\
           \ endstruct\n\
           \ let p = new Posn(1, 2), incx = p.incrX, incy = p.incrY in incx(); incx(); incy(); \
            incx(); incy(); p"
           "" "(Struct <2>: (4, 4, <closure field: 2>, <closure field: 3>) )";
         t "brain_transplant_operation1"
           "struct Posn = (x, y) in \n\
           \ method addUp(): self.x + self.y \n\
           \ endstruct let p = new Posn(1, 2) in print(p.addUp()); p.addUp := (lambda (n1, n2): n1 \
            + n2); p.addUp(5, 5)"
           "" "3\n10";
         t "two_structs_with_methods"
           "struct Posn = (x, y) in \n\
           \ method addUp(): self.x + self.y \n\
           \ endstruct\n\
           \ struct Posn3D = (x, y, z) in\n\
           \            method fromPosn(p: Posn): self.x := p.x; self.y := p.y; self.z := p.addUp()\n\
           \ endstruct\n\
           \           let p = new Posn(9, 9), p3 = new Posn3D(1, 2, 3) in p3.fromPosn(p); (p3.x, \
            p3.y, p3.z)"
           "" "(9, 9, 18)";
         t "two_structs_with_methods_construct"
           "struct Posn = (x, y) in \n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
            method fromCoords(x1, x2, y1, y2): new TwoPosn(new Posn(x1, y1), new Posn(x2, y2))\n\
           \ endstruct\n\
           \           let tp = new TwoPosn(nil, nil) in tp.fromCoords(1, 2, 3, 4)" ""
           "(Struct <3>: ((Struct <2>: (1, 3) ), (Struct <2>: (2, 4) ), <closure field: 2>) )";
         t "two_structs_with_two_methods_construct"
           "struct Posn = (x, y) in \n\
           \ method addUp(): self.x + self.y\n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
            method fromCoords(x1, x2, y1, y2): new TwoPosn(new Posn(x1, y1), new Posn(x2, y2))\n\
           \ endstruct\n\
           \           let tp = new TwoPosn(nil, nil) in tp.fromCoords(1, 2, 3, 4)" ""
           "(Struct <9>: ((Struct <2>: (1, 3, <closure field: 2>) ), (Struct <2>: (2, 4, <closure \
            field: 2>) ), <closure field: 2>) )";
         t "two_structs_with_two_methods_construct_apply"
           "struct Posn = (x, y) in \n\
           \ method addUp(): self.x + self.y\n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
            method fromCoords(x1, x2, y1, y2): new TwoPosn(new Posn(x1, y1), new Posn(x2, y2))\n\
           \ endstruct\n\
           \           let tp = new TwoPosn(nil, nil) in let tp = tp.fromCoords(1, 2, 3, 4) in\n\
           \ (tp.l.addUp(), tp.r.addUp())" "" "(4, 6)";
         t "struct_tuple_infer_good"
           "struct Posn = (x, y) in\n let p = new Posn(1, 2) in (1, p, 3)[1].y" "" "2";
         (* NOTE: due to the getitem expression having the index as an expression, *)
         (* we can only infer types out of tuples if that tuple only contains one struct type *)
         te "struct_tuple_infer_bad"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p = new Posn(1, 2), p3 = new Posn3D(1, 2, 3) in (p3, p, 3)[1].y" ""
           "a getter couldn't infer the type of a struct. try type hints";
         t "struct_tuple_infer_bad_workaround"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p = new Posn(1, 2), p3 = new Posn3D(1, 2, 3) in ((p3, p, 3)[1] as Posn).y" "" "2";
         (* NOTE: if either branch return a type related to a struct, then this EIf has that type.
                  however, if both branches return a "structy-type", and it isn't the same type, then
                  we can't infer a type.
         *)
         t "struct_if_infer_good1"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p2 = new Posn(4, 5) in (if true: p1 else: p2).x" "" "1";
         t "struct_if_infer_good2"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p2 = new Posn(4, 5) in (if false: p1 else: p2).x" "" "4";
         t "struct_if_infer_good3"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p2 = new Posn(4, 5) in (if true: p1 else: 99).x" "" "1";
         t "struct_if_infer_good4"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p2 = new Posn(4, 5) in (if false: 1 else: p2).x" "" "4";
         te "struct_if_infer_bad1"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p3 = new Posn3D(4, 5, 6) in (if true: p1 else: p3).x" ""
           "a getter couldn't infer the type of a struct. try type hints.";
         te "struct_if_infer_bad2"
           "struct Posn = (x, y) in\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ let p1 = new Posn(1, 2), p3 = new Posn3D(4, 5, 6) in (if false: p1 else: p3).x" ""
           "a getter couldn't infer the type of a struct. try type hints.";
         te "struct_construct_enforce_struct_type"
           "struct Posn = (x, y) in \n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
           \ endstruct\n\
           \ let tp = new TwoPosn(new Posn(1, 2), 5) in tp" ""
           "a constructor tried to set a struct field with a value of a different type";
         te "struct_setter_enforce_struct_type"
           "struct Posn = (x, y) in \n\
           \ endstruct\n\
           \ struct Posn3D = (x, y, z) in\n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
           \ endstruct\n\
           \ let tp = new TwoPosn(new Posn(1, 2), new Posn(4, 4)) in tp.l := new Posn3D(1, 2, 3); \
            tp"
           "" "a setter tried to set a struct field with a value of a different type";
         t "struct_method_print"
           "struct Cons = (first, rest: Cons) in\n\
           \       method printCons(): if (self.rest == nil): print(self.first) else: \
            print(self.first); self.rest.printCons()\n\
           \                  endstruct\n\
           \       let last_cons = new Cons(5, new Cons(4, new Cons(3, new Cons(2, new Cons(1, \
            nil))))) in\n\
           \       last_cons.printCons()" "" "5\n4\n3\n2\n1\n1";
         t "struct_method_self_equal_self"
           "struct Cons = (first, rest: Cons) in\n\
           \           method equals(): self == self\n\
            endstruct\n\
            let c = new Cons(1, nil) in c.equals()\n\
           \           " "" "true";
         t "struct_equal_self_args"
           "struct Cons = (first, rest: Cons) in \n\
           \           method equals(other): self == other \n\
            endstruct \n\
           \           let c = new Cons(3, nil) in c.equals(c)" "" "true";
         t "struct_dot_equals_true"
           "struct Posn = (x, y) in\n\
           \        method equals(other: Posn): (other is Posn) && (self.x == other.x) && (self.y \
            == other.y) endstruct\n\
           \        let p1 = new Posn(1, 2), p2 = new Posn(1, 2) in p1.equals(p2)\n\
           \        " "" "true";
         t "struct_dot_equals_false"
           "struct Posn = (x, y) in\n\
           \        method equals(other: Posn): (other is Posn) && (self.x == other.x) && (self.y \
            == other.y) endstruct\n\
           \        let p1 = new Posn(1, 2), p2 = new Posn(1, 3) in p1.equals(p2)\n\
           \        " "" "false";
         t "struct_same_method_name"
           "struct Posn = (x, y) in \n\
           \           method total(): self.x + self.y \n\
           \           endstruct \n\
           \           struct Posn3D = (x, y, z) in \n\
           \           method total(): self.x + self.y + self.z \n\
           \           endstruct \n\
           \           let p = new Posn(1, 2), p3d = new Posn3D(1, 2, 3) in p.total() + p3d.total()"
           "" "9";
         (* pass print, equals as first class functions in methods *)
         te "struct_brain_transplant_let_bound"
           "struct Cons = (first, rest: Cons) in\n\
           \          method renameSelf(): let self = 1 in self.first\n\
            endstruct\n\
            let c = new Cons(1, nil) in c.renameSelf()" "" "The identifier self, redefined";
         te "struct_brain_transplant_lambda_arg"
           "struct Cons = (first, rest: Cons) in\n\
           \          method renameSelf(): let f = (lambda (self): self + 1) in f(3)\n\
            endstruct\n\
            let c = new Cons(1, nil) in c.renameSelf()" "" "The identifier self, redefined";
         te "struct_brain_transplant_lambda_tuple_arg"
           "struct Cons = (first, rest: Cons) in\n\
           \          method renameSelf(): let f = (lambda ((self)): self + 1) in f((3))\n\
            endstruct\n\
            let c = new Cons(1, nil) in c.renameSelf()" "" "The identifier self, redefined";
         t "print_struct_in_method"
           "struct Posn = (x, y) in\n\
           \ method prettyPrint(): print((self.x, self.y, self))\n\
           \ endstruct\n\
            new Posn(4, 5).prettyPrint()" ""
           "(4, 5, (Struct <2>: (4, 5, <closure field: 2>) ))\n\
            (4, 5, (Struct <2>: (4, 5, <closure field: 2>) ))";
         t "struct_return_itself_chained"
           "struct Posn = (x, y) in\n\
           \ method retSelf(): self\n\
           \ endstruct\n\
            new Posn(4, 5).retSelf().retSelf().retSelf()" ""
           "(Struct <2>: (4, 5, <closure field: 2>) )";
         t "print_struct_in_method_chained"
           "struct Posn = (x, y) in\n\
           \ method printSelf(): print(self)\n\
           \ endstruct\n\
            new Posn(4, 5).printSelf().printSelf().printSelf()" ""
           "(Struct <2>: (4, 5, <closure field: 2>) )\n\
            (Struct <2>: (4, 5, <closure field: 2>) )\n\
            (Struct <2>: (4, 5, <closure field: 2>) )\n\
            (Struct <2>: (4, 5, <closure field: 2>) )";
         t "struct_method_lambda_param"
           "struct Posn = (x, y) in\n\
           \ method accept(visitor): visitor(self.x, self.y)\n\
           \ endstruct\n\
           \ let p = new Posn(5, 8), visit = (lambda (x, y): new Posn(x * 3, y * 3)) in \
            p.accept(visit)"
           "" "(Struct <2>: (15, 24, <closure field: 2>) )";
         t "struct_method_native_lambda_param"
           "struct Posn = (x, y) in\n\
           \ method accept(visitor): visitor(self.x, self.y)\n\
           \ endstruct\n\
           \ let p = new Posn(5, 8) in print(p.accept(equal)); p.x := 8; p.accept(equal)" ""
           "false\ntrue";
         t "struct_method_another_method_as_param"
           "struct Posn = (x, y) in\n\
           \ method accept(visitor): visitor(self.x, self.y)\n\
           \ endstruct\n\
           \ struct PosnMultVisitor = (mult) in\n\
           \ method apply(x, y): new Posn(x * self.mult, y * self.mult)\n\
           \ endstruct\n\
           \ let p = new Posn(5, 8), v = new PosnMultVisitor(3) in p.accept(v.apply)" ""
           "(Struct <2>: (15, 24, <closure field: 2>) )";
         t "cyclic_struct" "struct Ref = (r) in\n let ref = new Ref(nil) in ref.r := ref; ref" ""
           "(Struct <2>: (<cyclic struct 2>) )";
         tgc "cyclic_struct_gc_copy" 34
           "struct Ref = (r) in\n\
           \ let ref = new Ref(nil) in ref.r := ref; ref; (new Ref((1, 2, 3)), ref)" ""
           "((Struct <2>: ((1, 2, 3)) ), (Struct <2>: (<cyclic struct 3>) ))";
         tgc "struct_method_gc" 30
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct let p = new Posn(4, \
            4) in p.addUp()"
           "" "8";
         tgc "struct_method_gc_copy" 30
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct let p = new Posn(4, \
            4) in let g = p.addUp in g();g();g()"
           "" "8";
         tgc "two_structs_with_two_methods_construct_gc" 72
           "struct Posn = (x, y) in \n\
           \ method addUp(): self.x + self.y\n\
           \ endstruct\n\
           \ struct TwoPosn = (l: Posn, r: Posn) in\n\
            method fromCoords(x1, x2, y1, y2): new TwoPosn(new Posn(x1, y1), new Posn(x2, y2))\n\
           \ endstruct\n\
           \           let tp = new TwoPosn(nil, nil) in tp.fromCoords(1, 2, 3, 4)" ""
           "(Struct <9>: ((Struct <2>: (1, 3, <closure field: 2>) ), (Struct <2>: (2, 4, <closure \
            field: 2>) ), <closure field: 2>) )";
         te "let_rec_struct_arity"
           "struct Posn = (x, y) in endstruct let rec s = (lambda (x): new Posn(x)) in s" ""
           "The constructor called at <let_rec_struct_arity, 1:59-1:70> expected an arity of 2, \
            but received 1 arguments";
         te "let_rec_struct_arity2"
           "struct Posn = (x, y) in endstruct let rec s = (lambda (x, y, z): new Posn(x, y, z)) in \
            s"
           ""
           "The constructor called at <let_rec_struct_arity2, 1:65-1:82> expected an arity of 2, \
            but received 3 arguments";
         te "let_invalid_struct" "let s: Posn = 200 in s" ""
           "The struct name Posn, used at <let_invalid_struct, 1:4-1:11>, is not in scope";
         te "let_struct_arity" "struct Posn = (x, y) in endstruct let s = new Posn(1) in s" ""
           "The constructor called at <let_struct_arity, 1:42-1:53> expected an arity of 2, but \
            received 1 arguments";
         te "let_struct_arity2" "struct Posn = (x, y) in endstruct let s = new Posn(1, 2, 3) in s"
           ""
           "The constructor called at <let_struct_arity2, 1:42-1:59> expected an arity of 2, but \
            received 3 arguments";
         t "struct_method_with_input"
           "struct Posn = (x, y) in \n\
           \  method setValues(): let newX = input(), newY = input() in self.x := newX; self.y := \
            newY\n\
           \  endstruct\n\
           \  let p = new Posn(1, 2) in p.setValues(); print(p.x); print(p.y)" "3\n4\n" "3\n4\n4";
         t "method_decls"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct def f(x): x + new \
            Posn(x, 2).x\n\
           \ f(4)" "" "8";
         t "method_decls_call"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct def f(x): x + new \
            Posn(x, 2).addUp()\n\
           \ f(4)" "" "10";
         t "method_decl_ret_struct"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct def f(x): new \
            Posn(x, x * 2)\n\
           \ f(4)" "" "(Struct <2>: (4, 8, <closure field: 2>) )";
         t "method_decl_ret_struct_call_method"
           "struct Posn = (x, y) in method addUp(): self.x + self.y endstruct def f(x): new \
            Posn(x, x * 2)\n\
           \ f(4).addUp()" "" "12";
         te "method_decl_call_in_method"
           "struct Posn = (x, y) in method gen(): f(self.x) endstruct def f(x): new Posn(x, x * 2)\n\
           \ let p = new Posn(1, 2) in p.gen()" ""
           "The identifier f, used at <method_decl_call_in_method, 1:38-1:39>, is not in scope" ]

let () =
  run_test_tt_main
    ( "all_tests"
    >::: [ is_wf_suite;
           desugar_suite;
           rename_suite;
           free_vars_suite;
           alloc_suite;
           compile_fun_suite;
           compile_cexpr_suite;
           compile_aexpr_suite;
           compile_run_suite;
           lambda_suite;
           gc_suite;
           interfere_suite;
           color_graph_suite;
           reg_alloc_suite;
           fvs_cache_suite;
           struct_suite;
           input_file_test_suite () ] )
