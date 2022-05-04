open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Errors
open Graph
module StringSet = Set.Make (String)

type 'a name_envt = (string * 'a) list

type 'a tag_envt = (tag * 'a) list

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL

let const_false = HexConst 0x7FFFFFFFFFFFFFFFL

let bool_mask = HexConst 0x8000000000000000L

let bool_tag = 0x0000000000000007L

let bool_tag_mask = 0x0000000000000007L

let num_tag = 0x0000000000000000L

let num_tag_mask = 0x0000000000000001L

let closure_tag = 0x0000000000000005L

let closure_tag_mask = 0x0000000000000007L

let tuple_tag = 0x0000000000000001L

let tuple_tag_mask = 0x0000000000000007L

let struct_tag = 0x0000000000000003L

let struct_tag_mask = 0x0000000000000007L

let const_nil = HexConst tuple_tag

let err_COMP_NOT_NUM = 1L

let err_ARITH_NOT_NUM = 2L

let err_LOGIC_NOT_BOOL = 3L

let err_IF_NOT_BOOL = 4L

let err_OVERFLOW = 5L

let err_GET_NOT_TUPLE = 6L

let err_GET_LOW_INDEX = 7L

let err_GET_HIGH_INDEX = 8L

let err_NIL_DEREF = 9L

let err_OUT_OF_MEMORY = 10L

let err_SET_NOT_TUPLE = 11L

let err_SET_LOW_INDEX = 12L

let err_SET_HIGH_INDEX = 13L

let err_CALL_NOT_CLOSURE = 14L

let err_CALL_ARITY_ERR = 15L

let err_SET_NOT_NUM = 16L

let err_GET_NOT_NUM = 17L

let err_TUPLE_BAD_DESTRUCT = 18L

let err_GETTER_NOT_STRUCT = 19L

let err_SETTER_NOT_STRUCT = 20L

let err_GETTER_FIELD_NOT_FOUND = 21L

let err_SETTER_FIELD_NOT_FOUND = 22L

let err_SETTER_FIELD_WRONG_STRUCT = 23L

let err_CONSTRUCT_FIELD_WRONG_STRUCT = 24L

let dummy_span = (Lexing.dummy_pos, Lexing.dummy_pos)

let first_six_args_registers = [RDI; RSI; RDX; RCX; R8; R9]

let callee_saved_regs : arg list = [Reg R12; Reg R14; Reg RBX]

let reg_colors : arg list =
  [Reg R10; Reg R12; Reg R13; Reg R14; Reg RBX; Reg RDI; Reg RSI; Reg RDX; Reg R8; Reg R9]

let max_color_weight = List.length reg_colors - 1

let heap_reg = R15

let scratch_reg = R11

(* you can add any functions or data defined by the runtime here for future use *)
let wrappable_native_fun_env : int name_envt =
  [("input", 0); ("testarg", 9); ("equal", 2); ("print", 1)]

let natives_fun_env : int name_envt =
  wrappable_native_fun_env @ [("error", 2); ("our_code_starts_here", 2); ("printStack", 1)]

(* You may find some of these helpers useful *)

let find_pos ls x =
  let rec help ls i =
    match ls with
    | [] -> -1
    | y :: rest -> if y = x then i else help rest (i + 1)
  in
  help ls 0

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" (ExtLib.dump x)))
  | (y, v) :: rest -> if y = x then v else find rest x

let rec find_one_named (l : ('a * _) list) (name : 'a) : bool =
  match l with
  | [] -> false
  | (x, _) :: xs -> name = x || find_one_named xs name

let option_get (opt : 'a option) : 'a =
  match opt with
  | Some x -> x
  | _ -> raise (InternalCompilerError "Tried to unwrap an option that had none as a value")

(* looks up in the environment from the given tag and finds the first value named the given name *)
let rec find_in_env_tag (env : arg name_envt tag_envt) (name : string) (tag : tag) =
  match env with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found in tag-space: %d" name tag))
  | (env_tag, n_env) :: rest ->
      if env_tag = tag
      then try find n_env name with InternalCompilerError _ -> find_in_env_tag [] name tag
      else find_in_env_tag rest name tag

(* looks up all values in the nested environment and finds the first value named the given name *)
let rec find_in_env (env : arg name_envt tag_envt) (name : string) : arg =
  match env with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" name))
  | (_, n_env) :: rest -> (
    try find n_env name with InternalCompilerError _ -> find_in_env rest name )

let int_map (f : int -> 'a) (i : int) (start : int) : 'a list =
  let rec help (acc : int) = if acc = i then [] else f acc :: help (acc + 1) in
  help start

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
        List.length binds
        + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e

let rec replicate x i = if i = 0 then [] else x :: replicate x (i - 1)

let deepest_stack env =
  List.fold_left
    (fun max (_, arg) ->
      match arg with
      | RegOffset (si, RBP) ->
          let off = si * -1 / word_size in
          if off > max then off else max
      | _ -> max )
    0 env

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
      if name = fname then Some d else find_decl ds_rest name

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [x] -> None
  | x :: xs -> if find_one xs x then Some x else find_dup xs

let rec find_opt (env : 'a name_envt) (elt : string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst -> if x = elt then Some v else find_opt rst elt

(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 = list_env1 @ list_env2

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst) :: rst ->
        let rst_prepend = help rst env2 in
        if List.mem_assoc k env2 then rst_prepend else fst :: rst_prepend
  in
  help env1 env2

let env_keys e = List.map fst e

(* Represents the type of binding in the environment *)
type btype =
  | BTId
  | BTFun of int (* where int is the arity of the function *)
  | BTStruct of int
(* where int is the number of fields of the struct *)

(* Represents the information of a binding, with it's type of binding information *)
type bind_info = btype * sourcespan

(* Runs checks through the AST and either returns the program unchanged (if everything is good) *)
(* or returns a list of errors from the failed checks *)
let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  (* constant that defines the shadow environment, such that self cannot be redefined *)
  let self_bind = [BName ("self", false, dummy_span)] in
  (* Helper function to find a certain binding in the environment. *)
  let rec find_in_env (env : bind_info name_envt) ((x_name, x_btype) : string * btype) :
      bind_info option =
    match env with
    | [] -> None
    | (el_name, (el_btype, loc)) :: rest -> (
      match (x_btype, el_btype) with
      | (BTId, BTId | BTFun _, BTFun _ | BTStruct _, BTStruct _) when el_name = x_name ->
          Some (el_btype, loc)
      | _ -> find_in_env rest (x_name, x_btype) )
  in
  (* Checks whether a struct of the given name exists in the environment *)
  let check_unbound_stru_errs
      (stru_name : string)
      (stru_pos : sourcespan)
      (env : bind_info name_envt) : exn list =
    match find_in_env env (stru_name, BTStruct 0) with
    | None -> [UnboundStruct (stru_name, stru_pos)]
    | _ -> []
  in
  (* Checks for errors for the given binding and for duplicate bindings in the bind list *)
  let rec check_bind_errs
      (bind : sourcespan bind)
      (binds : sourcespan bind list)
      (env : bind_info name_envt) : exn list =
    (* Helper to get all duplicate binding errors *)
    let rec get_bind_dupes ((name, pos) as bname) (binds : sourcespan bind list) (err_acc : exn list)
        : exn list =
      match binds with
      | [] -> err_acc
      | BBlank _ :: rest -> get_bind_dupes bname rest err_acc
      | BName (dup_name, _, dup_pos) :: rest | BStruct (dup_name, _, dup_pos) :: rest ->
          if name = dup_name
          then get_bind_dupes bname rest (DuplicateId (name, pos, dup_pos) :: err_acc)
          else get_bind_dupes bname rest err_acc
      | BTuple (dup_binds, dup_pos) :: rest -> get_bind_dupes bname (dup_binds @ rest) err_acc
    in
    match bind with
    | BBlank _ -> []
    | BName (name, _, pos) -> get_bind_dupes (name, pos) binds []
    | BStruct (name, stru_name, pos) ->
        let unbound_stru_errs = check_unbound_stru_errs stru_name pos env in
        get_bind_dupes (name, pos) binds unbound_stru_errs
    | BTuple (dup_binds, pos) -> check_bind_list_errs (dup_binds @ binds) env
  and check_bind_list_errs (binds : sourcespan bind list) (env : bind_info name_envt) : exn list =
    (* Checks for duplicate bind names in a list of binds *)
    match binds with
    | [] -> []
    | bind :: rest -> check_bind_errs bind rest env @ check_bind_list_errs rest env
  in
  (* Adds the bind to the given environment, does not check for duplicates! *)
  let rec build_bind_env (bind : sourcespan bind) (env : bind_info name_envt) : bind_info name_envt
      =
    match bind with
    | BBlank _ -> env
    | BName (name, _, pos) | BStruct (name, _, pos) -> (name, (BTId, pos)) :: env
    | BTuple (binds, _) -> build_bind_list_env binds env
  and build_bind_list_env (binds : sourcespan bind list) (env : bind_info name_envt) :
      bind_info name_envt =
    (* Adds the binds in the bind list to the given environment, does not check for duplicates! *)
    List.fold_left (fun prev_env b -> build_bind_env b prev_env) env binds
  in
  (* Helper function to run a well-formed check on a single expression. *)
  let rec wf_E (env : bind_info name_envt) (e : sourcespan expr) : exn list =
    match e with
    | EBool _ -> []
    | ENil _ -> []
    | ENumber (i, loc) ->
        (* Checks if the number is between bounds *)
        if i > Int64.div Int64.max_int 2L || i < Int64.div Int64.min_int 2L
        then [Overflow (i, loc)]
        else []
    | EId (x, loc) ->
        (* Checks if the given identifier is in the environment *)
        if find_one_named env x then [] else [UnboundId (x, loc)]
    | EPrim1 (_, body, _) -> wf_E env body
    | EPrim2 (_, l, r, _) -> wf_E env l @ wf_E env r
    | EIf (c, t, f, _) -> wf_E env c @ wf_E env t @ wf_E env f
    | ELet (bindings, body, loc) ->
        let env', _, errs =
          List.fold_left
            (fun (prev_env, prev_binds, prev_errs) binding ->
              let bind, e, b_pos = binding in
              let bind_errs = check_bind_errs bind prev_binds env in
              let expr_errs = wf_E prev_env e in
              let env' = build_bind_env bind prev_env in
              (env', bind :: prev_binds, expr_errs @ bind_errs @ prev_errs) )
            (env, self_bind, []) bindings
        in
        wf_E env' body @ errs
    | EApp (func, args, cl, loc) ->
        let arity = List.length args in
        let call_errs =
          match func with
          | EId (name, _) -> (
            match find_in_env env (name, BTFun arity) with
            | Some (BTFun env_arity, _) when env_arity != arity -> [Arity (env_arity, arity, loc)]
            | _ -> [] )
          | _ -> []
        in
        let funexpr_errs = wf_E env func in
        let args_errs = List.concat_map (fun a -> wf_E env a) args in
        call_errs @ funexpr_errs @ args_errs
    | EConstruct (stru_name, fields, pos) ->
        let arity = List.length fields in
        let unbound_stru_errs, env_res =
          match find_in_env env (stru_name, BTStruct arity) with
          | Some (BTStruct env_arity, env_pos) -> ([], Some (env_arity, env_pos))
          | None | Some _ -> ([UnboundStruct (stru_name, pos)], None)
        in
        let arity_errs =
          match env_res with
          | Some (env_arity, env_pos) ->
              if env_arity = arity then [] else [StructArity (env_arity, arity, pos)]
          | None -> []
        in
        unbound_stru_errs @ arity_errs @ List.concat_map (fun e -> wf_E env e) fields
    | EGetter (expr, field, _) ->
        (* NOTE: there is no way without a type system we could check if the field exists or not *)
        wf_E env expr
    | ESetter (expr, field, new_expr, _) ->
        (* NOTE: there is no way without a type system we could check if the field exists or not *)
        wf_E env expr @ wf_E env new_expr
    | EIs (e, stru_name, pos) | EAs (e, stru_name, pos) ->
        let unbound_stru_errs = check_unbound_stru_errs stru_name pos env in
        unbound_stru_errs @ wf_E env e
    | ETuple (exprs, _) -> List.concat_map (fun e -> wf_E env e) exprs
    | ESeq (l, r, _) -> wf_E env l @ wf_E env r
    | EGetItem (e, index, _) -> wf_E env e @ wf_E env index
    | ESetItem (e, index, new_e, _) -> wf_E env e @ wf_E env index @ wf_E env new_e
    | ELambda (binds, body, _) ->
        let bind_errs = check_bind_list_errs (self_bind @ binds) env in
        let env' = build_bind_list_env binds env in
        bind_errs @ wf_E env' body
    | ELetRec (bindings, body, _) ->
        let env', _, bind_errs =
          List.fold_left
            (fun (prev_env, prev_binds, prev_errs) binding ->
              let bind, e, b_pos = binding in
              let bind_errs = check_bind_errs bind prev_binds env in
              let env' = build_bind_env bind prev_env in
              let letrec_non_function_errs =
                match e with
                | ELambda _ -> []
                | _ -> [LetRecNonFunction (bind, b_pos)]
              in
              (env', bind :: prev_binds, letrec_non_function_errs @ bind_errs @ prev_errs) )
            (env, self_bind, []) bindings
        in
        let lambda_errs = List.concat_map (fun (_, expr, _) -> wf_E env' expr) bindings in
        lambda_errs @ bind_errs @ wf_E env' body
  and wf_D (env : bind_info name_envt) (d : sourcespan decl) : exn list =
    match d with
    | DFun (funname, binds, body, loc) ->
        let body_env = build_bind_list_env binds env in
        wf_E body_env body @ check_bind_list_errs binds env
  and wf_DG (env : bind_info name_envt) (ds : sourcespan decl list) : exn list * bind_info name_envt
      =
    (* Helper function to build an environment of declaration names, in order to allow mutually referential functions *)
    let rec build_decls_env (env : bind_info name_envt) (decls : sourcespan decl list) :
        exn list * bind_info name_envt =
      match decls with
      | [] -> ([], [])
      | DFun (name, args, body, loc) :: rest ->
          let arity = List.length args in
          (* Checks for duplicate function names in the environment *)
          let fun_dup_errs =
            match find_in_env env (name, BTFun arity) with
            | Some (BTFun env_arity, env_loc) -> [DuplicateFun (name, loc, env_loc)]
            | _ -> []
          in
          let decl_env = [(name, (BTFun arity, loc))] in
          let next_errs, next_env = build_decls_env decl_env rest in
          (fun_dup_errs @ next_errs, decl_env @ next_env)
    in
    (* Builds the function name environment from each declaration *)
    let decls_errs, decls_env = build_decls_env env ds in
    let decl_inner_errs = List.concat_map (fun d -> wf_D (decls_env @ env) d) ds in
    (decl_inner_errs @ decls_errs, decls_env)
  (* Helper function to run a well-formed check on a single method. *)
  and wf_M (env : bind_info name_envt) (m : 'a mthd) (stru_name : string) :
      exn list * (string * bind_info) =
    match m with
    | DMethod (name, binds, body, pos) ->
        let arity = List.length binds in
        let method_dup_err =
          match find_in_env env (name, BTFun arity) with
          | Some (BTFun env_arity, env_loc) -> [DuplicateMethod (name, pos, env_loc)]
          | _ -> []
        in
        let self_binding = BStruct ("self", stru_name, pos) in
        let env_entry = (name, (BTFun arity, pos)) in
        let body_env = build_bind_list_env (self_binding :: binds) (env @ [env_entry]) in
        let arg_dup_errs = check_bind_list_errs (self_binding :: binds) env in
        let body_errs = wf_E body_env body in
        (method_dup_err @ arg_dup_errs @ body_errs, env_entry)
  (* Helper function to run a well-formed check on a single struct. *)
  and wf_S (env : bind_info name_envt) (s : 'a stru) : exn list * bind_info name_envt =
    match s with
    | DStruct (stru_name, fields, methods, pos) ->
        let arity = List.length fields in
        let env_entries = [(stru_name, (BTStruct arity, pos))] in
        let env' = env_entries @ env in
        let rec process_field_errs (fields : sourcespan strufield list) =
          let rec get_dupes (name : string) (fields : sourcespan strufield list) =
            match fields with
            | [] -> []
            | FName dup_name :: rest ->
                if name = dup_name then [DuplicateField (name, pos)] else get_dupes name rest
            | FStruct (dup_name, _) :: rest ->
                if name = dup_name then [DuplicateField (name, pos)] else get_dupes name rest
            | _ ->
                raise (InternalCompilerError "FMethod fields shouldn't be generated in well_formed")
          in
          match fields with
          | [] -> []
          | FName name :: rest -> get_dupes name rest @ process_field_errs rest
          | FStruct (name, stru_name) :: rest ->
              let dup_errs = get_dupes name rest in
              let unbound_stru_errs = check_unbound_stru_errs stru_name pos env' in
              dup_errs @ unbound_stru_errs @ process_field_errs rest
          | _ -> raise (InternalCompilerError "FMethod fields shouldn't be generated in well_formed")
        in
        let dup_stru_errs =
          match find_in_env env (stru_name, BTStruct arity) with
          | Some (BTStruct _, env_pos) -> [DuplicateStruct (stru_name, pos, env_pos)]
          | _ -> []
        in
        let mthds_errs, mthds_env =
          List.fold_left
            (fun (prev_errs, prev_env) m ->
              let mthd_errs, ((mthd_name, (_, mthd_pos)) as mthd_entry) =
                wf_M (prev_env @ env') m stru_name
              in
              let clashing_field_err =
                List.fold_left
                  (fun next f ->
                    let name =
                      match f with
                      | FName name -> name
                      | FStruct (name, _) -> name
                      | _ ->
                          raise
                            (InternalCompilerError
                               "FMethod fields shouldn't be generated in well_formed" )
                    in
                    if name = mthd_name then [DuplicateField (name, mthd_pos)] @ next else next )
                  [] fields
              in
              (mthd_errs @ clashing_field_err @ prev_errs, mthd_entry :: prev_env) )
            ([], []) methods
        in
        let field_errs = process_field_errs fields in
        (dup_stru_errs @ mthds_errs @ field_errs, env_entries)
  in
  match p with
  | Program (strus, decls_groups, body, _) -> (
      (* builds initial environment from builtins *)
      let builtins_env =
        List.map
          (fun (name, arity) -> (name, (BTFun arity, (Lexing.dummy_pos, Lexing.dummy_pos))))
          natives_fun_env
      in
      (* finds errors and builds environment from structs *)
      let stru_errs, stru_env =
        List.fold_left
          (fun (prev_errs, prev_env) stru ->
            let errs, env' = wf_S prev_env stru in
            (errs @ prev_errs, env' @ prev_env) )
          ([], builtins_env) strus
      in
      (* finds errors and builds environment from decls *)
      let dg_errs, dg_env =
        List.fold_right
          (fun decls (prev_errs, prev_env) ->
            let errs, env = wf_DG stru_env decls in
            (errs @ prev_errs, env @ prev_env) )
          decls_groups ([], stru_env)
      in
      match wf_E dg_env body @ dg_errs @ stru_errs with
      | [] -> Ok p
      | errs -> Error errs )

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)
(* represents an environment of structs to their methods name and their desugared expressions. *)
type 'a cenv = (string * 'a expr) list name_envt

let desugar (p : 'a program) : 'a program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s?%d" name !next
  in
  (* helper to patch the given methods into fields of a constructor *)
  let patch_methods stru_id stru_name methods =
    let info = expr_info stru_id in
    List.fold_left
      (fun next_e name ->
        ESeq
          ( ESetter
              ( EAs (stru_id, stru_name, info),
                name,
                EApp (EId ("tempcurry_" ^ name, info), [stru_id], Snake, info),
                info ),
            next_e,
            info ) )
      stru_id methods
  in
  let rec desugar_E (e : 'a expr) (cenv : 'a cenv) : 'a expr =
    (* Helper function to desugar a binding. Assumes that for a tuple binding, the binding pattern matches
       the shape of the bound tuple. Desugar based on the pattern. *)
    let rec desugar_binding (b : 'a binding) : 'a binding list =
      match b with
      | BBlank bpos, e, pos -> [(BBlank bpos, desugar_E e cenv, pos)]
      | BName (name, shadow, bpos), e, pos -> [(BName (name, shadow, bpos), desugar_E e cenv, pos)]
      | BStruct (name, stru_name, bpos), e, pos ->
          [(BStruct (name, stru_name, bpos), desugar_E e cenv, pos)]
      | BTuple (binds, bpos), rhs, pos ->
          let temp_name = gensym "tup" in
          let temp_id = EId (temp_name, bpos) in
          [ (BName (temp_name, false, bpos), rhs, pos);
            ( BBlank pos,
              EPrim2 (CheckSize, temp_id, ENumber (Int64.of_int (List.length binds), pos), pos),
              pos ) ]
          @ List.concat
              (List.mapi
                 (fun i b ->
                   desugar_binding
                     (b, EGetItem (temp_id, ENumber (Int64.of_int i, bpos), bpos), bpos) )
                 binds )
    in
    match e with
    | EBool _ -> e
    | ENumber _ -> e
    | ENil _ -> e
    | EId _ -> e
    | EPrim1 (op, e, info) -> EPrim1 (op, desugar_E e cenv, info)
    | EPrim2 (op, l, r, info) -> (
        (* Double negates the given expression to ensure that a Boolean error is thrown if the expression is not bool *)
        let double_negate (e : 'a expr) : 'a expr =
          EPrim1 (Not, EPrim1 (Not, e, expr_info e), expr_info e)
        in
        let desugared_l = double_negate (desugar_E l cenv) in
        let desugared_r = double_negate (desugar_E r cenv) in
        (* Desugars and/or into ifs to preserve short-circuiting semantics *)
        match op with
        | And -> EIf (desugared_l, desugared_r, desugared_l, info)
        | Or -> EIf (desugared_l, desugared_l, desugared_r, info)
        | _ -> EPrim2 (op, desugar_E l cenv, desugar_E r cenv, info) )
    | EIf (c, t, f, info) -> EIf (desugar_E c cenv, desugar_E t cenv, desugar_E f cenv, info)
    | EApp (func, args, call_type, info) ->
        EApp (desugar_E func cenv, List.map (fun a -> desugar_E a cenv) args, call_type, info)
    | ELet (bindings, body, info) ->
        ELet (List.concat (List.map desugar_binding bindings), desugar_E body cenv, info)
    | ETuple (exprs, info) -> ETuple (List.map (fun e -> desugar_E e cenv) exprs, info)
    | EGetItem (e, index, info) -> EGetItem (desugar_E e cenv, desugar_E index cenv, info)
    | ESetItem (e, index, new_e, info) ->
        ESetItem (desugar_E e cenv, desugar_E index cenv, desugar_E new_e cenv, info)
    | ESeq (l, r, info) -> ELet ([(BBlank info, desugar_E l cenv, info)], desugar_E r cenv, info)
    | ELambda (binds, body, info) ->
        let rec desugar_bind (b : 'a bind) : 'a bind list * 'a binding list =
          match b with
          | BBlank binfo -> ([BName ("_", false, binfo)], [])
          | BName (name, shadow, binfo) -> ([BName (name, shadow, binfo)], [])
          | BStruct (name, stru_name, binfo) -> ([BStruct (name, stru_name, binfo)], [])
          | BTuple (binds, binfo) ->
              let temp_name = gensym "arg_tup" in
              let temp_bind = BName (temp_name, false, binfo) in
              let temp_id = EId (temp_name, binfo) in
              let temp_binding = (b, temp_id, binfo) in
              ([temp_bind], [temp_binding])
        in
        let desugared_binds, body_bindings =
          List.fold_right
            (fun bind (prev_bs, prev_bings) ->
              let bs, bings = desugar_bind bind in
              (bs @ prev_bs, bings @ prev_bings) )
            binds ([], [])
        in
        let des_body =
          match body_bindings with
          | [] -> desugar_E body cenv
          | _ -> desugar_E (ELet (body_bindings, body, info)) cenv
        in
        ELambda (desugared_binds, des_body, info)
    | ELetRec (bindings, body, info) ->
        ELetRec (List.concat (List.map desugar_binding bindings), desugar_E body cenv, info)
    | EConstruct (stru_name, fields, info) -> (
        (* when we encounter a constructor, we check if that constructor has any methods, if not, we don't *)
        (* patch the methods. if it does have methods, we check if we have desugared this constructor already *)
        (* (this might be the body of a method), if wwe have, we don't patch methods. otherwise, we patch *)
        (* the methods of this constructor to be curried (on the self parameter) first-class functions. *)
        let maybe_methods = find_opt cenv stru_name in
        match maybe_methods with
        | None -> EConstruct (stru_name, List.map (fun f -> desugar_E f cenv) fields, info)
        | Some ms when List.length ms = 0 ->
            EConstruct (stru_name, List.map (fun f -> desugar_E f cenv) fields, info)
        | Some methods ->
            let temp_stru_inner = gensym stru_name in
            let stru_id_inner = EId (temp_stru_inner, info) in
            let methods_bindings =
              List.map
                (fun (name, body) ->
                  ( BName ("tempcurry_" ^ name, false, info),
                    ELambda ([BStruct ("self", stru_name, info)], body, info),
                    info ) )
                methods
            in
            let unpatched_construct =
              EConstruct
                ( stru_name,
                  List.map (fun f -> desugar_E f cenv) fields
                  @ List.map (fun _ -> ENil info) methods,
                  info )
            in
            let method_names = List.map (fun (name, _) -> name) methods in
            let patched_methods = patch_methods stru_id_inner stru_name method_names in
            let letrecs = ELetRec (methods_bindings, patched_methods, info) in
            ELet
              ( [(BStruct (temp_stru_inner, stru_name, info), unpatched_construct, info)],
                letrecs,
                info ) )
    | EGetter (expr, field, info) -> EGetter (desugar_E expr cenv, field, info)
    | ESetter (expr, field, new_expr, info) ->
        ESetter (desugar_E expr cenv, field, desugar_E new_expr cenv, info)
    | EIs (e, stru_name, info) -> EIs (desugar_E e cenv, stru_name, info)
    | EAs (e, stru_name, info) -> EAs (desugar_E e cenv, stru_name, info)
  (* helper to desugar a decl *)
  and desugar_D (d : 'a decl) (cenv : 'a cenv) : 'a binding =
    match d with
    | DFun (funname, binds, body, info) ->
        (BName (funname, false, info), desugar_E (ELambda (binds, body, info)) cenv, info)
  (* helper to desugar a struct. it additionally generates a cenv from this struct and the previous struct *)
  and desugar_S (s : 'a stru) (cenv : 'a cenv) : 'a stru * 'a cenv =
    match s with
    | DStruct (sname, fields, mthds, tag) ->
        let method_names =
          List.map
            (fun m ->
              match m with
              | DMethod (name, _, _, _) -> name )
            mthds
        in
        (* helper to desugar a method. generates the environment entry for this method. *)
        let rec desugar_M (m : 'a mthd) : 'a strufield * (string * 'a expr) =
          match m with
          | DMethod (name, binds, body, tag) ->
              (* helper to recur on expressions. *)
              let rec helpE (e : 'a expr) =
                match e with
                | ESeq (e1, e2, t) -> ESeq (helpE e1, helpE e2, t)
                | ETuple (exprs, tag) -> ETuple (List.map helpE exprs, tag)
                | EConstruct (stru_name, fields, tag) ->
                    (* when we encounter a constructor: if the constructor is constructing the current struct, *)
                    (* then we desugar it to include the patched methods. otherwise we recur on the fields. *)
                    if stru_name = sname
                    then
                      let stru_temp = gensym stru_name in
                      let stru_id = EId (stru_temp, tag) in
                      let method_fields =
                        List.map (fun name -> EGetter (EId ("self", tag), name, tag)) method_names
                      in
                      let patched_methods = patch_methods stru_id stru_name method_names in
                      ELet
                        ( [ ( BStruct (stru_temp, stru_name, tag),
                              EConstruct (stru_name, List.map helpE fields @ method_fields, tag),
                              tag ) ],
                          patched_methods,
                          tag )
                    else EConstruct (stru_name, List.map helpE fields, tag)
                | EGetter (expr, field, tag) -> EGetter (helpE expr, field, tag)
                | ESetter (expr, field, new_expr, tag) ->
                    ESetter (helpE expr, field, helpE new_expr, tag)
                | EIs (e, stru_name, tag) -> EIs (helpE e, stru_name, tag)
                | EAs (e, stru_name, tag) -> EAs (helpE e, stru_name, tag)
                | EGetItem (e, idx, tag) -> EGetItem (helpE e, helpE idx, tag)
                | ESetItem (e, idx, newval, tag) -> ESetItem (helpE e, helpE idx, helpE newval, tag)
                | EId (x, tag) -> EId (x, tag)
                | ENumber (n, tag) -> ENumber (n, tag)
                | EBool (b, tag) -> EBool (b, tag)
                | ENil tag -> ENil tag
                | EPrim1 (op, e, tag) -> EPrim1 (op, helpE e, tag)
                | EPrim2 (op, e1, e2, tag) -> EPrim2 (op, helpE e1, helpE e2, tag)
                | ELet (binds, body, tag) ->
                    ELet (List.map (fun (b, e, tag) -> (b, helpE e, tag)) binds, helpE body, tag)
                | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
                | EApp (func, args, native, tag) ->
                    EApp (helpE func, List.map helpE args, native, tag)
                | ELetRec (binds, body, tag) ->
                    ELetRec (List.map (fun (b, e, tag) -> (b, helpE e, tag)) binds, helpE body, tag)
                | ELambda (binds, body, tag) -> ELambda (binds, helpE body, tag)
              in
              (* we fully-desugar the body in order to desugar potential constructors from other structs. *)
              (* NOTE: we don't create duplicate code, as we have a check in desugar_E to verify if the constructor *)
              (* needs to be desugared or not. *)
              let reconstructed_body = ELambda (binds, helpE body, tag) in
              let desugared_body = desugar_E reconstructed_body cenv in
              (FMethod (name, binds, desugared_body), (name, desugared_body))
        in
        let fmethods, env_entries =
          List.fold_left
            (fun (prev_fms, prev_env) m ->
              let fm, env = desugar_M m in
              (fm :: prev_fms, env :: prev_env) )
            ([], []) mthds
        in
        (DStruct (sname, fields @ List.rev fmethods, [], tag), [(sname, env_entries)])
  in
  match p with
  | Program (strus, dgs, body, info) ->
      let desugared_strus, cenv =
        List.fold_left
          (fun (prev_st, prev_env) s ->
            let st, env = desugar_S s prev_env in
            (st :: prev_st, env @ prev_env) )
          ([], []) strus
      in
      let desguared_groups =
        List.fold_right
          (fun decls prev_expr ->
            let bindings = List.map (fun d -> desugar_D d cenv) decls in
            ELetRec (bindings, prev_expr, info) )
          dgs (desugar_E body cenv)
      in
      Program (List.rev desugared_strus, [], desguared_groups, info)

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (strus, decls, body, tag) ->
        Program
          ( List.map (helpS env) strus,
            List.map (fun group -> List.map (helpD env) group) decls,
            helpE env body,
            tag )
  and helpM env m =
    match m with
    | DMethod (name, binds, body, tag) -> DMethod (name, binds, helpE env body, tag)
  and helpF env f =
    match f with
    | FMethod (name, binds, body) ->
        let binds', env' = helpBS env binds in
        FMethod (name, binds', helpE (env' @ env) body)
    | _ -> f
  and helpS env s =
    match s with
    | DStruct (name, fields, methods, tag) ->
        DStruct (name, List.map (helpF env) fields, List.map (helpM env) methods, tag)
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
        let newArgs, env' = helpBS env args in
        DFun (name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank tag -> (b, env)
    | BName (name, allow_shadow, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BName (name', allow_shadow, tag), (name, name') :: env)
    | BStruct (name, stru_name, tag) ->
        let name' = sprintf "%s_%d" name tag in
        (BStruct (name', stru_name, tag), (name, name') :: env)
    | BTuple (binds, tag) ->
        let binds', env' = helpBS env binds in
        (BTuple (binds', tag), env')
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> ([], env)
    | b :: bs ->
        let b', env' = helpB env b in
        let bs', env'' = helpBS env' bs in
        (b' :: bs', env'')
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> ([], env)
    | (b, e, a) :: bindings ->
        let b', env' = helpB env b in
        let e' = helpE env e in
        let bindings', env'' = helpBG env' bindings in
        ((b', e', a) :: bindings', env'')
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EConstruct (stru_name, fields, tag) -> EConstruct (stru_name, List.map (helpE env) fields, tag)
    | EGetter (expr, field, tag) -> EGetter (helpE env expr, field, tag)
    | ESetter (expr, field, new_expr, tag) ->
        ESetter (helpE env expr, field, helpE env new_expr, tag)
    | EIs (e, stru_name, tag) -> EIs (helpE env e, stru_name, tag)
    | EAs (e, stru_name, tag) -> EAs (helpE env e, stru_name, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) -> ( try EId (find env name, tag) with InternalCompilerError _ -> e )
    | EApp (func, args, native, tag) -> (
      match func with
      | EId (name, _) when find_one_named natives_fun_env name ->
          EApp (func, List.map (helpE env) args, Native, tag)
      | _ ->
          let func = helpE env func in
          EApp (func, List.map (helpE env) args, Snake, tag) )
    | ELet (binds, body, tag) ->
        let binds', env' = helpBG env binds in
        let body' = helpE env' body in
        ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
        let revbinds, env =
          List.fold_left
            (fun (revbinds, env) (b, e, t) ->
              let b, env = helpB env b in
              ((b, e, t) :: revbinds, env) )
            ([], env) bindings
        in
        let bindings' =
          List.fold_left (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings) [] revbinds
        in
        let body' = helpE env body in
        ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
        let binds', env' = helpBS env binds in
        let body' = helpE env' body in
        ELambda (binds', body', tag)
  in
  rename [] p

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; STRUCT SYMBOL TABLE GENERATION ;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

(* helper to return the type of a type-tagged expr *)
let e_ty (e : (strutype * tag) expr) : strutype = (fun (ty, _) -> ty) (expr_info e)

(* tries to infer the struct type of the given expression, if it has one *)
(* used to figure out getter/setter struct types, and type annotates the expressions *)
let rec inferP (p : tag program) : (strutype * tag) program =
  let rec inferE (e : tag expr) (env : styenv) : (strutype * tag) expr =
    match e with
    | ESeq (e1, e2, tag) ->
        let e2_ans = inferE e2 env in
        ESeq (inferE e1 env, e2_ans, (e_ty e2_ans, tag))
    | ETuple (exprs, tag) ->
        (* NOTE: all of the tuple elements have to be the same type (ok to have some STNone) to be infered *)
        let elem_ans = List.map (fun e -> inferE e env) exprs in
        let elem_types = List.map (fun e -> e_ty e) elem_ans in
        (* filter out all STNone *)
        let struct_types =
          List.filter
            (fun st ->
              match st with
              | STNone -> false
              | _ -> true )
            elem_types
        in
        let ty =
          match struct_types with
          | x :: xs when List.fold_left (fun prev t -> x = t && prev) true xs -> STTup x
          | _ -> STTup STNone
        in
        ETuple (elem_ans, (ty, tag))
    | EConstruct (stru_name, fields, tag) ->
        EConstruct (stru_name, List.map (fun f -> inferE f env) fields, (STSome stru_name, tag))
    | EGetter (expr, field, tag) ->
        let expr_ans = inferE expr env in
        let ty =
          match e_ty expr_ans with
          | STSome stru_name ->
              List.fold_left
                (fun next (sb, st) ->
                  match sb with
                  | SBField name when field = name -> st
                  | _ -> next )
                STNone env
          | _ -> STNone
        in
        EGetter (expr_ans, field, (ty, tag))
    | ESetter (expr, field, new_expr, tag) ->
        let new_e_ans = inferE new_expr env in
        ESetter (inferE expr env, field, new_e_ans, (e_ty new_e_ans, tag))
    | EIs (e, stru_name, tag) -> EIs (inferE e env, stru_name, (STNone, tag))
    | EAs (e, stru_name, tag) -> EAs (inferE e env, stru_name, (STSome stru_name, tag))
    | EGetItem (e, idx, tag) ->
        (* NOTE: all of the tuple elements have to be the same type to be infered *)
        let e_ans = inferE e env in
        let ty =
          match e_ty e_ans with
          | STTup s -> s
          | _ -> STNone
        in
        EGetItem (e_ans, inferE idx env, (ty, tag))
    | ESetItem (e, idx, newval, tag) ->
        let newval_ans = inferE newval env in
        ESetItem (inferE e env, inferE idx env, newval_ans, (e_ty newval_ans, tag))
    | EId (x, tag) ->
        let ty =
          List.fold_left
            (fun next (sb, st) ->
              match sb with
              | SBId name when x = name -> st
              | _ -> next )
            STNone env
        in
        EId (x, (ty, tag))
    | ENumber (n, tag) -> ENumber (n, (STNone, tag))
    | EBool (b, tag) -> EBool (b, (STNone, tag))
    | ENil tag -> ENil (STNone, tag)
    | EPrim1 (op, e, tag) -> EPrim1 (op, inferE e env, (STNone, tag))
    | EPrim2 (op, e1, e2, tag) -> EPrim2 (op, inferE e1 env, inferE e2 env, (STNone, tag))
    | ELet (bindings, body, tag) ->
        let env', binds_ans = inferBS bindings env in
        let body_ans = inferE body (env' @ env) in
        ELet (binds_ans, body_ans, (e_ty body_ans, tag))
    | ELetRec (binds, body, tag) ->
        let unpatched, _ = inferBS binds env in
        let patched =
          List.fold_left
            (fun next (sb, st) ->
              match st with
              | STClos (binds, body, fenv) -> (sb, STClos (binds, body, unpatched @ fenv)) :: next
              | _ -> next )
            [] unpatched
        in
        let _, binds_ans = inferBS binds (patched @ env) in
        let body_ans = inferE body (patched @ env) in
        ELetRec (binds_ans, body_ans, (e_ty body_ans, tag))
    | EIf (cond, thn, els, tag) ->
        (* NOTE: if either branch return a type related to a struct, then this EIf has that type.
                 however, if both branches return a "structy-type", and it isn't the same type, then
                 we can't infer a type.
        *)
        let then_res = inferE thn env in
        let then_ty = e_ty then_res in
        let else_res = inferE els env in
        let else_ty = e_ty else_res in
        let ty =
          match (then_ty, else_ty) with
          | STSome s1, STSome s2 when s1 = s2 -> STSome s1
          | STSome s, STNone -> STSome s
          | STNone, STSome s -> STSome s
          | STClos _, STNone -> then_ty
          | STNone, STClos _ -> else_ty
          | STTup _, STNone -> then_ty
          | STNone, STTup _ -> else_ty
          | _ -> STNone
        in
        EIf (inferE cond env, then_res, else_res, (ty, tag))
    | EApp ((EId (name, idtag) as func), args, Native, tag) -> (
      match name with
      | "print" ->
          let a_ans = inferE (List.hd args) env in
          EApp (inferE func env, [a_ans], Native, (e_ty a_ans, tag))
      | _ -> EApp (inferE func env, List.map (fun a -> inferE a env) args, Native, (STNone, tag)) )
    | EApp (func, args, native, tag) ->
        let func_res = inferE func env in
        let ty, args_res =
          match e_ty func_res with
          (* NOTE: edge case: when an application has an arity mismatch. *)
          | STClos (bind_tys, fun_body, fenv) when List.length bind_tys = List.length args ->
              let infenv, args_res =
                List.fold_left2
                  (fun (prev_env, prev_res) cb a ->
                    let a_res = inferE a env in
                    let tya = e_ty a_res in
                    match cb with
                    | name, STSome stru_name ->
                        ((SBId name, STSome stru_name) :: prev_env, a_res :: prev_res)
                    | name, _ -> ((SBId name, tya) :: prev_env, a_res :: prev_res) )
                  ([], []) bind_tys args
              in
              (e_ty (inferE fun_body (infenv @ fenv)), List.rev args_res)
          | other -> (other, List.map (fun a -> inferE a env) args)
        in
        EApp (func_res, args_res, native, (ty, tag))
    | ELambda (binds, body, tag) ->
        let binds_typed, env', binds_ans = inferB binds env in
        let ty = STClos (binds_typed, body, env) in
        ELambda (binds_ans, inferE body env', (ty, tag))
  (* Tries to infer types from the given binds, and generates an environment from them. *)
  (* Additionally, returns a mapping of bind name to bind strutype and the new binds that have been type-annotated *)
  and inferB (binds : tag bind list) (env : styenv) :
      (string * strutype) list * styenv * (strutype * tag) bind list =
    let tybinds, env', binds' =
      List.fold_left
        (fun (prev_ty, prev_env, prev_ans) b ->
          match b with
          | BName (name, s, tag) ->
              let ty = STNone in
              ( (name, ty) :: prev_ty,
                (SBId name, ty) :: prev_env,
                BName (name, s, (ty, tag)) :: prev_ans )
          | BStruct (name, stru_name, tag) ->
              let ty = STSome stru_name in
              ( (name, ty) :: prev_ty,
                (SBId name, ty) :: prev_env,
                BStruct (name, stru_name, (ty, tag)) :: prev_ans )
          | BBlank tag ->
              let ty = STNone in
              (("_", ty) :: prev_ty, (SBId "_", ty) :: prev_env, BBlank (ty, tag) :: prev_ans)
              (* NOTE: assumes the program is desugared, so we can't have tuple bindings *)
          | _ -> raise (InternalCompilerError "Tuple bindings reached inference phase") )
        ([], env, []) binds
    in
    (List.rev tybinds, env', List.rev binds')
  (* Tries to infer types from the given bindings, and generates an environment from them. *)
  (* Additionally, returns new bindings that have been type-annotated *)
  and inferBS (bindings : tag binding list) (env : styenv) : styenv * (strutype * tag) binding list
      =
    let env', binds' =
      List.fold_left
        (fun (prev_env, prev_binds) b ->
          match b with
          | BStruct (name, stru_name, btag), e, tag ->
              let entry = (SBId name, STSome stru_name) in
              let e_ans = inferE e (prev_env @ env) in
              ( entry :: prev_env,
                (BStruct (name, stru_name, (STSome stru_name, btag)), e_ans, (e_ty e_ans, tag))
                :: prev_binds )
          | BName (name, s, btag), e, tag ->
              let e_ans = inferE e (prev_env @ env) in
              let ty = e_ty e_ans in
              let stru_entry =
                match ty with
                | STNone -> []
                | st -> [(SBId name, st)]
              in
              (stru_entry @ prev_env, (BName (name, s, (ty, btag)), e_ans, (ty, tag)) :: prev_binds)
          | BBlank btag, e, tag ->
              let e_ans = inferE e (prev_env @ env) in
              (prev_env, (BBlank (e_ty e_ans, btag), e_ans, (e_ty e_ans, tag)) :: prev_binds)
          (* NOTE: assumes the program is desugared, so we can't have tuple bindings *)
          | _ -> raise (InternalCompilerError "Tuple bindings reached inference phase") )
        ([], []) bindings
    in
    (env', List.rev binds')
  (* infers types from struct fields and returns a new environment of those types. *)
  (* additionally, returns the type-annotated struct *)
  and inferS (s : tag stru) (env : styenv) : (strutype * tag) stru * styenv =
    match s with
    | DStruct (stru_name, fields, [], tag) ->
        let tyenv, fields_ans =
          List.fold_left
            (fun (prev_tyenv, prev_ans) f ->
              match f with
              | FName name -> (prev_tyenv, FName name :: prev_ans)
              | FStruct (name, stru_name) ->
                  ( (SBField name, STSome stru_name) :: prev_tyenv,
                    FStruct (name, stru_name) :: prev_ans )
              | FMethod (name, binds, body) ->
                  let binds_typed, env', binds_ans = inferB binds (env @ prev_tyenv) in
                  let body_env = [(SBId "self", STSome stru_name)] @ env' @ prev_tyenv @ env in
                  let body_ans = inferE body body_env in
                  ( (SBField name, e_ty body_ans) :: prev_tyenv,
                    FMethod (name, binds_ans, body_ans) :: prev_ans ) )
            ([], []) fields
        in
        (DStruct (stru_name, List.rev fields_ans, [], (STSome stru_name, tag)), tyenv)
    | _ -> raise (InternalCompilerError "inferP was called on a program that hasn't been desugared")
  in
  match p with
  | Program (strus, [], body, tag) ->
      let strus_ans, tyenv =
        List.fold_left
          (fun (prev_strus, prev_tyenv) s ->
            let s_ans, tyenv = inferS s prev_tyenv in
            (s_ans :: prev_strus, prev_tyenv @ tyenv) )
          ([], []) strus
      in
      let body_ans = inferE body tyenv in
      Program (List.rev strus_ans, [], body_ans, (e_ty body_ans, tag))
  | _ -> raise (InternalCompilerError "inferP was called on a program that hasn't been desugared")

(* represents a struct with its possible struct fields *)
type struident = stru_id * stru_id option list

(* Represents a symbol table for structs and their unique ids and field offsets *)
(* where the optional id indicates weather that field should be holding another struct *)
type struenv = struident * (field_offset * stru_id option) name_envt

type strutbl = struenv HashMap.t

(* generates a table mapping AST tags to struct unique tags and field offsets *)
(* ASSUMES program has been desugared *)
let gensymtbl (p : tag program) : tag program * symboltbl =
  (* where tbl is the symbol table of structs, and env is mapping from ids to structs (if they are structs) *)
  let rec helpE (e : (strutype * tag) expr) (tbl : strutbl) : symboltbl =
    (* Helper to get the field offset of the given field, from the given struct expression *)
    let get_offset (e : (strutype * tag) expr) (field : string) : stru_field_tag =
      (* Bogus offsets, so that in the runtime it throws. -1 for type errors, -2 for not found errors *)
      let bogus_off_type_err = {offset= -1; uid= -1; field_uid= None} in
      let bogus_off_not_found = {offset= -2; uid= -2; field_uid= None} in
      match e_ty e with
      | STSome stru_name -> (
          let (unique_id, _), stru_fields = HashMap.find stru_name tbl in
          match find_opt stru_fields field with
          | Some (found_offset, field_struid) ->
              {offset= found_offset; uid= unique_id; field_uid= field_struid}
          | None -> bogus_off_not_found )
      | _ -> bogus_off_type_err
    in
    match e with
    | ESeq (e1, e2, tag) -> helpE e1 tbl @ helpE e2 tbl
    | ETuple (exprs, tag) -> List.concat_map (fun e -> helpE e tbl) exprs
    | EConstruct (stru_name, fields, (_, tag)) ->
        let (unique_id, field_ids), _ = HashMap.find stru_name tbl in
        [(tag, Either.left {uid= unique_id; field_uids= field_ids})]
        @ List.concat_map (fun e -> helpE e tbl) fields
    | EGetter (expr, field, (_, tag)) ->
        let offset = get_offset expr field in
        [(tag, Either.right offset)] @ helpE expr tbl
    | ESetter (expr, field, new_expr, (_, tag)) ->
        let offset = get_offset expr field in
        [(tag, Either.right offset)] @ helpE expr tbl @ helpE new_expr tbl
    | EIs (e, stru_name, (_, tag)) ->
        let (unique_id, field_ids), _ = HashMap.find stru_name tbl in
        [(tag, Either.left {uid= unique_id; field_uids= field_ids})] @ helpE e tbl
    | EAs (e, stru_name, _) -> helpE e tbl
    | EGetItem (e, idx, tag) -> helpE e tbl @ helpE idx tbl
    | ESetItem (e, idx, newval, tag) -> helpE e tbl @ helpE idx tbl @ helpE newval tbl
    | EId (x, tag) -> []
    | ENumber (n, tag) -> []
    | EBool (b, tag) -> []
    | ENil tag -> []
    | EPrim1 (op, e, tag) -> helpE e tbl
    | EPrim2 (op, e1, e2, tag) -> helpE e1 tbl @ helpE e2 tbl
    | ELet (bindings, body, tag) ->
        let bindings_res = List.concat_map (fun (_, e, _) -> helpE e tbl) bindings in
        bindings_res @ helpE body tbl
    | ELetRec (bindings, body, tag) ->
        let bindings_res = List.concat_map (fun (_, e, _) -> helpE e tbl) bindings in
        bindings_res @ helpE body tbl
    | EIf (cond, thn, els, tag) -> helpE cond tbl @ helpE thn tbl @ helpE els tbl
    | EApp (func, args, native, tag) -> helpE func tbl @ List.concat_map (fun a -> helpE a tbl) args
    | ELambda (binds, body, tag) -> helpE body tbl
  (* Generates the symbol table entry and the type environment for the given struct *)
  and helpS (s : (strutype * tag) stru) (tbl : strutbl) : string * struenv =
    match s with
    | DStruct (stru_name, fields, methods, (_, tag)) ->
        let env, field_ids, _ =
          List.fold_left
            (fun (prev_env, prev_fids, i) f ->
              match f with
              | FName name -> ((name, (i + 2, None)) :: prev_env, None :: prev_fids, i + 1)
              | FStruct (name, stru_field_name) ->
                  let soffset =
                    if stru_name = stru_field_name
                    then Some tag
                    else
                      let (unique_id, _), _ = HashMap.find stru_field_name tbl in
                      Some unique_id
                  in
                  ((name, (i + 2, soffset)) :: prev_env, soffset :: prev_fids, i + 1)
              | FMethod (name, _, _) -> ((name, (i + 2, None)) :: prev_env, None :: prev_fids, i + 1)
              )
            ([], [], 0) fields
        in
        (stru_name, ((tag, List.rev field_ids), env))
  in
  match inferP p with
  | Program (strus, _, body, _) ->
      let strutbl =
        List.fold_left
          (fun prev_tbl s ->
            let stru_name, env = helpS s prev_tbl in
            HashMap.add stru_name env prev_tbl )
          HashMap.empty strus
      in
      (p, helpE body strutbl)

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) (stbl : symboltbl) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program (_, _, body, _) -> AProgram (helpA body, ())
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
    match e with
    | EPrim1 (op, arg, _) ->
        let arg_imm, arg_setup = helpI arg in
        (CPrim1 (op, arg_imm, ()), arg_setup)
    | EPrim2 (op, left, right, _) ->
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        (CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf (cond, _then, _else, _) ->
        let cond_imm, cond_setup = helpI cond in
        (CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec (binds, body, _) ->
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        (body_ans, BLetRec (List.combine names new_binds) :: body_setup)
    | ELambda (args, body, _) ->
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | BStruct (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        (CLambda (List.map processBind args, helpA body, ()), [])
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EApp (func, args, native, _) ->
        let func_ans, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        (CApp (func_ans, new_args, native, ()), func_setup @ List.concat new_setup)
    | ESeq (e1, e2, _) ->
        let e1_ans, e1_setup = helpC e1 in
        let e2_ans, e2_setup = helpC e2 in
        (e2_ans, e1_setup @ [BSeq e1_ans] @ e2_setup)
    | ETuple (args, _) ->
        let new_args, new_setup = List.split (List.map helpI args) in
        (CTuple (new_args, ()), List.concat new_setup)
    | EGetItem (tup, idx, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (CGetItem (tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem (tup, idx, newval, _) ->
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        (CSetItem (tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup)
    | EConstruct (stru_name, fields, tag) ->
        let new_fields, new_setup = List.split (List.map helpI fields) in
        let unique_id = option_get (Either.find_left (find stbl tag)) in
        (CConstruct (unique_id, new_fields, ()), List.concat new_setup)
    | EGetter (stru_expr, field_name, tag) ->
        let stru_imm, stru_setup = helpI stru_expr in
        let offset = option_get (Either.find_right (find stbl tag)) in
        (CGetter (stru_imm, offset, ()), stru_setup)
    | ESetter (stru_expr, field_name, new_field, tag) ->
        let stru_imm, stru_setup = helpI stru_expr in
        let offset = option_get (Either.find_right (find stbl tag)) in
        let new_imm, new_setup = helpI new_field in
        (CSetter (stru_imm, offset, new_imm, ()), stru_setup @ new_setup)
    | EIs (e, stru_name, tag) ->
        let e_imm, e_setup = helpI e in
        let unique_id = option_get (Either.find_left (find stbl tag)) in
        (CIs (e_imm, unique_id, ()), e_setup)
    | _ ->
        let imm, setup = helpI e in
        (CImmExpr imm, setup)
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> (ImmNum (n, ()), [])
    | EBool (b, _) -> (ImmBool (b, ()), [])
    | EId (name, _) -> (ImmId (name, ()), [])
    | ENil _ -> (ImmNil (), [])
    | ESeq (e1, e2, _) ->
        let e1_imm, e1_setup = helpI e1 in
        let e2_imm, e2_setup = helpI e2 in
        (e2_imm, e1_setup @ e2_setup)
    | ETuple (args, tag) ->
        let tmp = sprintf "tup_%d" tag in
        let new_args, new_setup = List.split (List.map helpI args) in
        (ImmId (tmp, ()), List.concat new_setup @ [BLet (tmp, CTuple (new_args, ()))])
    | EGetItem (tup, idx, tag) ->
        let tmp = sprintf "get_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        (ImmId (tmp, ()), tup_setup @ idx_setup @ [BLet (tmp, CGetItem (tup_imm, idx_imm, ()))])
    | ESetItem (tup, idx, newval, tag) ->
        let tmp = sprintf "set_%d" tag in
        let tup_imm, tup_setup = helpI tup in
        let idx_imm, idx_setup = helpI idx in
        let new_imm, new_setup = helpI newval in
        ( ImmId (tmp, ()),
          tup_setup @ idx_setup @ new_setup @ [BLet (tmp, CSetItem (tup_imm, idx_imm, new_imm, ()))]
        )
    | EConstruct (stru_name, fields, tag) ->
        let tmp = sprintf "new_%s_%d" stru_name tag in
        let new_fields, new_setup = List.split (List.map helpI fields) in
        let unique_id = option_get (Either.find_left (find stbl tag)) in
        ( ImmId (tmp, ()),
          List.concat new_setup @ [BLet (tmp, CConstruct (unique_id, new_fields, ()))] )
    | EGetter (stru_expr, field_name, tag) ->
        let tmp = sprintf "getter_%s_%d" field_name tag in
        let stru_imm, stru_setup = helpI stru_expr in
        let offset = option_get (Either.find_right (find stbl tag)) in
        (ImmId (tmp, ()), stru_setup @ [BLet (tmp, CGetter (stru_imm, offset, ()))])
    | ESetter (stru_expr, field_name, new_field, tag) ->
        let tmp = sprintf "setter_%s_%d" field_name tag in
        let stru_imm, stru_setup = helpI stru_expr in
        let new_field_imm, new_field_setup = helpI new_field in
        let offset = option_get (Either.find_right (find stbl tag)) in
        (ImmId (tmp, ()), stru_setup @ [BLet (tmp, CSetter (stru_imm, offset, new_field_imm, ()))])
    | EIs (e, stru_name, tag) ->
        let tmp = sprintf "is_%s_%d" stru_name tag in
        let e_imm, e_setup = helpI e in
        let unique_id = option_get (Either.find_left (find stbl tag)) in
        (ImmId (tmp, ()), e_setup @ [BLet (tmp, CIs (e_imm, unique_id, ()))])
    | EAs (e, stru_name, tag) ->
        (* NOTE: EAs doesn't get directly translated, we translate only the nested expression *)
        helpI e
    | EPrim1 (op, arg, tag) ->
        let tmp = sprintf "unary_%d" tag in
        let arg_imm, arg_setup = helpI arg in
        (ImmId (tmp, ()), arg_setup @ [BLet (tmp, CPrim1 (op, arg_imm, ()))])
    | EPrim2 (op, left, right, tag) ->
        let tmp = sprintf "binop_%d" tag in
        let left_imm, left_setup = helpI left in
        let right_imm, right_setup = helpI right in
        ( ImmId (tmp, ()),
          left_setup @ right_setup @ [BLet (tmp, CPrim2 (op, left_imm, right_imm, ()))] )
    | EIf (cond, _then, _else, tag) ->
        let tmp = sprintf "if_%d" tag in
        let cond_imm, cond_setup = helpI cond in
        (ImmId (tmp, ()), cond_setup @ [BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ()))])
    | EApp (func, args, native, tag) ->
        let tmp = sprintf "app_%d" tag in
        let new_func, func_setup = helpI func in
        let new_args, new_setup = List.split (List.map helpI args) in
        ( ImmId (tmp, ()),
          func_setup @ List.concat new_setup @ [BLet (tmp, CApp (new_func, new_args, native, ()))]
        )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BSeq exp_ans] @ body_setup)
    | ELetRec (binds, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind (bind, rhs, _) =
          match bind with
          | BName (name, _, _) -> (name, helpC rhs)
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a let-rec: %s"
                      (string_of_bind bind) ) )
        in
        let names, new_binds_setup = List.split (List.map processBind binds) in
        let new_binds, new_setup = List.split new_binds_setup in
        let body_ans, body_setup = helpC body in
        ( ImmId (tmp, ()),
          List.concat new_setup
          @ [BLetRec (List.combine names new_binds)]
          @ body_setup
          @ [BLet (tmp, body_ans)] )
    | ELambda (args, body, tag) ->
        let tmp = sprintf "lam_%d" tag in
        let processBind bind =
          match bind with
          | BName (name, _, _) -> name
          | BStruct (name, _, _) -> name
          | _ ->
              raise
                (InternalCompilerError
                   (sprintf "Encountered a non-simple binding in ANFing a lambda: %s"
                      (string_of_bind bind) ) )
        in
        (ImmId (tmp, ()), [BLet (tmp, CLambda (List.map processBind args, helpA body, ()))])
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BStruct (bind, _, _), exp, _) :: rest, body, pos) ->
        let exp_ans, exp_setup = helpC exp in
        let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
        (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
        raise (InternalCompilerError "Tuple bindings should have been desugared away")
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()) )
      ans_setup (ACExpr ans)
  in
  helpP p

let rec free_vars_aexpr (e : 'a aexpr) (bound_env : StringSet.t) : StringSet.t =
  match e with
  | ASeq (l, r, _) -> StringSet.union (free_vars_cexpr l bound_env) (free_vars_aexpr r bound_env)
  | ALet (name, c_e, a_body, _) ->
      let binding_free_vars = free_vars_cexpr c_e bound_env in
      let new_env = StringSet.add name bound_env in
      let body_free_vars = free_vars_aexpr a_body new_env in
      StringSet.union binding_free_vars body_free_vars
  | ALetRec (bindings, a_body, _) ->
      let new_env =
        List.fold_left (fun prev_env (name, _) -> StringSet.add name prev_env) bound_env bindings
      in
      let binding_free_vars =
        List.fold_left
          (fun prev_vars (_, c_e) -> StringSet.union (free_vars_cexpr c_e new_env) prev_vars)
          StringSet.empty bindings
      in
      let body_free_vars = free_vars_aexpr a_body new_env in
      StringSet.union binding_free_vars body_free_vars
  | ACExpr c_e -> free_vars_cexpr c_e bound_env

and free_vars_cexpr (e : 'a cexpr) (bound_env : StringSet.t) : StringSet.t =
  match e with
  | CIf (imm_cond, a_then, a_else, _) ->
      let cond_free_vars = free_vars_immexpr imm_cond bound_env in
      let then_free_vars = free_vars_aexpr a_then bound_env in
      let else_free_vars = free_vars_aexpr a_else bound_env in
      StringSet.union cond_free_vars (StringSet.union then_free_vars else_free_vars)
  | CPrim1 (_, imm_e, _) -> free_vars_immexpr imm_e bound_env
  | CPrim2 (_, left, right, _) ->
      StringSet.union (free_vars_immexpr left bound_env) (free_vars_immexpr right bound_env)
  | CLambda (binds, body, _) ->
      let new_env = StringSet.union bound_env (StringSet.of_list binds) in
      free_vars_aexpr body new_env
  | CApp (_, imm_args, Native, _) ->
      List.fold_left
        (fun prev_free_vars elem ->
          StringSet.union prev_free_vars (free_vars_immexpr elem bound_env) )
        StringSet.empty imm_args
  | CApp (func, imm_args, _, _) ->
      let arg_fvs =
        List.fold_left
          (fun prev_free_vars elem ->
            StringSet.union prev_free_vars (free_vars_immexpr elem bound_env) )
          StringSet.empty imm_args
      in
      StringSet.union (free_vars_immexpr func bound_env) arg_fvs
  | CTuple (elems, _) ->
      List.fold_left
        (fun prev_free_vars elem ->
          StringSet.union prev_free_vars (free_vars_immexpr elem bound_env) )
        StringSet.empty elems
  | CGetItem (imm_tup, imm_i, _) ->
      StringSet.union (free_vars_immexpr imm_tup bound_env) (free_vars_immexpr imm_i bound_env)
  | CSetItem (imm_tup, imm_i, imm_new, _) ->
      let tup_free_vars = free_vars_immexpr imm_tup bound_env in
      let i_free_vars = free_vars_immexpr imm_i bound_env in
      let new_free_vars = free_vars_immexpr imm_new bound_env in
      StringSet.union tup_free_vars (StringSet.union i_free_vars new_free_vars)
  | CConstruct (_, fields, _) ->
      List.fold_left
        (fun prev_free_vars elem ->
          StringSet.union prev_free_vars (free_vars_immexpr elem bound_env) )
        StringSet.empty fields
  | CGetter (imm_stru, _, _) -> free_vars_immexpr imm_stru bound_env
  | CSetter (imm_stru, _, imm_new_field, _) ->
      StringSet.union
        (free_vars_immexpr imm_stru bound_env)
        (free_vars_immexpr imm_new_field bound_env)
  | CIs (imm_stru, _, _) -> free_vars_immexpr imm_stru bound_env
  | CImmExpr imm_e -> free_vars_immexpr imm_e bound_env

and free_vars_immexpr (e : 'a immexpr) (bound_env : StringSet.t) : StringSet.t =
  match e with
  | ImmId (name, _) -> (
    match StringSet.find_opt name bound_env with
    | Some _ -> StringSet.empty
    | None -> StringSet.add name StringSet.empty )
  | _ -> StringSet.empty

(* Where bound_env is the set of bound variables *)
let free_vars (e : 'a aexpr) : string list = StringSet.elements (free_vars_aexpr e StringSet.empty)

(* Book-keeping accessor helpers *)
let imm_fvs (i : (StringSet.t * tag) immexpr) : StringSet.t = immexpr_info i (fun (fvs, _) -> fvs)

let cexpr_fvs (c : (StringSet.t * tag) cexpr) : StringSet.t = cexpr_info c (fun (fvs, _) -> fvs)

let aexpr_fvs (a : (StringSet.t * tag) aexpr) : StringSet.t = aexpr_info a (fun (fvs, _) -> fvs)

(* Caches the free variables of every single expression into their bookkeeping slot *)
(* NOTE: we changed the signature to produce an AST that is both tagged and has free variables *)
(*       such that we could utilize our tagged environment while preserving the free variables *)
let rec free_vars_cache (prog : tag aprogram) : (StringSet.t * tag) aprogram =
  match prog with
  | AProgram (body, tag) ->
      let body_ans = fvc_A body StringSet.empty in
      AProgram (body_ans, (aexpr_fvs body_ans, tag))
(* Where bound_env is the set of bound variables *)

and fvc_A (e : tag aexpr) (bound_env : StringSet.t) : (StringSet.t * tag) aexpr =
  match e with
  | ASeq (l, r, tag) ->
      let l_ans = fvc_C l bound_env in
      let r_ans = fvc_A r bound_env in
      ASeq (l_ans, r_ans, (StringSet.union (cexpr_fvs l_ans) (aexpr_fvs r_ans), tag))
  | ALet (name, c_e, a_body, tag) ->
      let e_ans = fvc_C c_e bound_env in
      let new_env = StringSet.add name bound_env in
      let body_fvs = free_vars_aexpr a_body new_env in
      let body_unbound = fvc_A a_body bound_env in
      ALet (name, e_ans, body_unbound, (StringSet.union (cexpr_fvs e_ans) body_fvs, tag))
  | ALetRec (bindings, a_body, tag) ->
      let new_env =
        List.fold_left (fun prev_env (name, _) -> StringSet.add name prev_env) bound_env bindings
      in
      let bindings_ans, bindings_fvs =
        List.fold_right
          (fun (name, c_e) (prev_binds, prev_fvs) ->
            let e_fvs = free_vars_cexpr c_e new_env in
            ((name, fvc_C c_e bound_env) :: prev_binds, StringSet.union e_fvs prev_fvs) )
          bindings ([], StringSet.empty)
      in
      let body_fvs = free_vars_aexpr a_body new_env in
      ALetRec (bindings_ans, fvc_A a_body bound_env, (StringSet.union bindings_fvs body_fvs, tag))
  | ACExpr c_e -> ACExpr (fvc_C c_e bound_env)

and fvc_C (e : tag cexpr) (bound_env : StringSet.t) : (StringSet.t * tag) cexpr =
  let fold_imms (imms : tag immexpr list) : (StringSet.t * tag) immexpr list * StringSet.t =
    List.fold_right
      (fun imm (prev_imms, prev_fvs) ->
        let imm_ans = fvc_I imm bound_env in
        (imm_ans :: prev_imms, StringSet.union prev_fvs (imm_fvs imm_ans)) )
      imms ([], StringSet.empty)
  in
  match e with
  | CIf (imm_cond, a_then, a_else, tag) ->
      let cond_ans = fvc_I imm_cond bound_env in
      let then_ans = fvc_A a_then bound_env in
      let else_ans = fvc_A a_else bound_env in
      CIf
        ( cond_ans,
          then_ans,
          else_ans,
          ( StringSet.union (imm_fvs cond_ans)
              (StringSet.union (aexpr_fvs then_ans) (aexpr_fvs else_ans)),
            tag ) )
  | CPrim1 (op, imm_e, tag) ->
      let imm_ans = fvc_I imm_e bound_env in
      CPrim1 (op, imm_ans, (imm_fvs imm_ans, tag))
  | CPrim2 (op, left, right, tag) ->
      let left_ans = fvc_I left bound_env in
      let right_ans = fvc_I right bound_env in
      CPrim2 (op, left_ans, right_ans, (StringSet.union (imm_fvs left_ans) (imm_fvs right_ans), tag))
  | CLambda (binds, body, tag) ->
      let new_env = StringSet.union bound_env (StringSet.of_list binds) in
      let body_ans = fvc_A body new_env in
      let body_unbound = fvc_A body bound_env in
      CLambda (binds, body_unbound, (aexpr_fvs body_ans, tag))
  | CApp (ImmId (name, id_tag), imm_args, Native, tag) ->
      (* NOTE: we handle the native func call such that the id is not a free variable *)
      let args_ans, fvs = fold_imms imm_args in
      CApp (ImmId (name, (StringSet.empty, id_tag)), args_ans, Native, (fvs, tag))
  | CApp (func, imm_args, _, tag) ->
      let args_ans, fvs = fold_imms imm_args in
      let func_ans = fvc_I func bound_env in
      CApp (func_ans, args_ans, Snake, (StringSet.union fvs (imm_fvs func_ans), tag))
  | CTuple (elems, tag) ->
      let elems_ans, fvs = fold_imms elems in
      CTuple (elems_ans, (fvs, tag))
  | CGetItem (imm_tup, imm_i, tag) ->
      let tup_ans = fvc_I imm_tup bound_env in
      let i_ans = fvc_I imm_i bound_env in
      CGetItem (tup_ans, i_ans, (StringSet.union (imm_fvs tup_ans) (imm_fvs i_ans), tag))
  | CSetItem (imm_tup, imm_i, imm_new, tag) ->
      let tup_ans = fvc_I imm_tup bound_env in
      let i_ans = fvc_I imm_i bound_env in
      let new_ans = fvc_I imm_new bound_env in
      CSetItem
        ( tup_ans,
          i_ans,
          new_ans,
          ( StringSet.union (imm_fvs new_ans) (StringSet.union (imm_fvs tup_ans) (imm_fvs i_ans)),
            tag ) )
  | CConstruct (struid, fields, tag) ->
      let field_ans, fvs = fold_imms fields in
      CConstruct (struid, field_ans, (fvs, tag))
  | CGetter (imm_stru, offset, tag) ->
      let stru_ans = fvc_I imm_stru bound_env in
      CGetter (stru_ans, offset, (imm_fvs stru_ans, tag))
  | CSetter (imm_stru, offset, imm_new_field, tag) ->
      let stru_ans = fvc_I imm_stru bound_env in
      let field_ans = fvc_I imm_new_field bound_env in
      CSetter
        (stru_ans, offset, field_ans, (StringSet.union (imm_fvs stru_ans) (imm_fvs field_ans), tag))
  | CIs (imm, unique, tag) ->
      let imm_ans = fvc_I imm bound_env in
      CIs (imm_ans, unique, (imm_fvs imm_ans, tag))
  | CImmExpr imm_e -> CImmExpr (fvc_I imm_e bound_env)

and fvc_I (e : tag immexpr) (bound_env : StringSet.t) : (StringSet.t * tag) immexpr =
  match e with
  | ImmId (name, tag) -> (
    match StringSet.find_opt name bound_env with
    | Some _ -> ImmId (name, (StringSet.empty, tag))
    | None -> ImmId (name, (StringSet.add name StringSet.empty, tag)) )
  | ImmNum (n, tag) -> ImmNum (n, (StringSet.empty, tag))
  | ImmNil tag -> ImmNil (StringSet.empty, tag)
  | ImmBool (b, tag) -> ImmBool (b, (StringSet.empty, tag))

(* Creates a nested environment mapping closure tags to stack locations. *)
(* DESIGN DECISION: we chose to utilize tags instead of strings as we wouldn't need to change the anf *)
(*                  phase, and we would only need to be careful about not retagging the AST *)
let naive_stack_allocation (prog : (StringSet.t * tag) aprogram) :
    (StringSet.t * tag) aprogram * arg name_envt tag_envt =
  (* merges commonly-tagged environments into one. NOTE: assumes environment is sorted *)
  let rec merge_common_envs (t_env : arg name_envt tag_envt) =
    match t_env with
    | [] -> []
    | [x] -> [x]
    | (tag1, env1) :: rest ->
        let rec split_envs env acc =
          match env with
          | [] -> (acc, [])
          | (tag2, env2) :: rest -> if tag1 = tag2 then split_envs rest (acc @ env2) else (acc, env)
        in
        let common, uncommon = split_envs rest env1 in
        (tag1, common) :: merge_common_envs uncommon
  in
  let rec alloc_A (a : 'a aexpr) (si : int) (prev_tag : int) : arg name_envt tag_envt * int =
    match a with
    | ALet (name, c_e, a_body, _) ->
        let c_env, c_si = alloc_C c_e (si + 1) prev_tag in
        let a_body_env, a_body_si = alloc_A a_body (si + 1) prev_tag in
        ( [(prev_tag, [(name, RegOffset (~-(si * word_size), RBP))])] @ c_env @ a_body_env,
          max c_si a_body_si )
    | ASeq (e1, e2, _) ->
        let c_env, c_si = alloc_C e1 si prev_tag in
        let a_body_env, a_body_si = alloc_A e2 si prev_tag in
        (c_env @ a_body_env, max c_si a_body_si)
    | ALetRec (binds, a_body, _) ->
        let binds_env, _ =
          List.fold_left
            (fun (prev_env, prev_si) (name, c_e) ->
              let c_env, _ = alloc_C c_e si prev_tag in
              ( [(prev_tag, [(name, RegOffset (~-(prev_si * word_size), RBP))])] @ c_env @ prev_env,
                prev_si + 1 ) )
            ([], si) binds
        in
        let a_body_env, a_body_si = alloc_A a_body (si + 1) prev_tag in
        (binds_env @ a_body_env, a_body_si)
    | ACExpr c_e -> alloc_C c_e si prev_tag
  and alloc_C (c : 'a cexpr) (si : int) (prev_tag : int) : arg name_envt tag_envt * int =
    match c with
    | CIf (_, a_then, a_else, _) ->
        let then_env, then_si = alloc_A a_then si prev_tag in
        let else_env, _ = alloc_A a_else then_si prev_tag in
        (then_env @ else_env, si)
    | CLambda (args, body, (fvs, tag)) ->
        let fvs = List.sort compare (StringSet.elements fvs) in
        let arg_env = List.mapi (fun i name -> (name, RegOffset ((3 + i) * word_size, RBP))) args in
        let body_env, body_si = alloc_A body si tag in
        let fvs_env, _ =
          List.fold_right
            (fun name (prev_env, i) ->
              let arg = RegOffset (~-word_size * i, RBP) in
              let env_entry = (name, arg) in
              (env_entry :: prev_env, i + 1) )
            fvs ([], 1)
        in
        (body_env @ [(tag, arg_env @ fvs_env)], 1)
    | _ -> ([], si)
  in
  match prog with
  | AProgram (a_body, (_, tag)) ->
      let body_env, _ = alloc_A a_body 1 tag in
      let merged_env =
        merge_common_envs
          (List.sort (fun (tag1, _) (tag2, _) -> tag1 - tag2) ((tag, []) :: body_env))
      in
      (prog, merged_env)

(* Generates an interference graph of the variables in our AST *)
let rec interfere (e : (StringSet.t * tag) aexpr) (live : StringSet.t) (remove : StringSet.t) :
    grapht =
  (* helper to recur on cexprs, where we want to recur on if expressions and merge the
     environments of both branches *)
  let rec helpC (c : (StringSet.t * tag) cexpr) : grapht =
    match c with
    | CIf (cond, t, f, (fvs, tag)) -> merge (interfere t live remove) (interfere f live remove)
    | _ -> empty
  in
  match e with
  | ASeq (bind, body, (fvs, _)) -> merge (helpC bind) (interfere body live remove)
  | ALet (name, bind, body, (fvs, _)) ->
      let interf = StringSet.elements (StringSet.union (StringSet.diff fvs remove) live) in
      let graph =
        List.fold_right
          (fun fv prev_graph -> add_edge prev_graph name fv)
          interf
          (add_node (helpC bind) name)
      in
      merge graph (interfere body (StringSet.add name live) remove)
  | ALetRec (bindings, body, (fvs, _)) ->
      let names, exprs =
        List.fold_right
          (fun (name, e) (prev_names, prev_es) -> (name :: prev_names, e :: prev_es))
          bindings ([], [])
      in
      let fvs_lams =
        StringSet.diff
          (List.fold_left
             (fun prev_fvs ce -> StringSet.union prev_fvs (cexpr_fvs ce))
             StringSet.empty exprs )
          remove
      in
      let bind_interf =
        List.fold_left
          (fun prev_interf name ->
            StringSet.fold (fun fv_name interf -> add_edge interf fv_name name) fvs_lams prev_interf
            )
          empty names
      in
      let names = StringSet.of_list names in
      let live' = StringSet.union names live in
      let graph = pairup bind_interf live' in
      merge graph (interfere body live' remove)
  | ACExpr x -> helpC x

(* Produces an environment with variables bound to registers or stack slots depending on the *)
(* coloring of the given graph that is going to be produced *)
let color_graph (g : grapht) (init_env : arg name_envt) : arg name_envt =
  (* Generates the worklist needed for coloring the graph *)
  (* NOTE: worklist needs to be reversed at the end *)
  let rec generate_worklist (g : grapht) (gd : grapht_deg) (acc : string list) : string list =
    if List.length acc = List.length (Graph.bindings g)
    then acc
    else
      (* NOTE: this sorts the degrees in reverse, such that the highest comes first *)
      let sorted_degs = List.sort (fun (_, d1) (_, d2) -> d2 - d1) (HashMap.bindings gd) in
      let highest_name, highest_dg = List.hd sorted_degs in
      let worklist = highest_name :: acc in
      let neighbors = get_neighbors g highest_name in
      (* NOTE: we don't remove the node from the actual graph, instead we remove it from the *)
      (*       hashmap of degrees, and we decrement the degree of every neighbor by one *)
      let new_gd =
        HashMap.mapi
          (fun name deg ->
            match List.find_opt (fun neigh_name -> neigh_name = name) neighbors with
            | None -> deg
            | Some _ -> deg - 1 )
          (HashMap.remove highest_name gd)
      in
      generate_worklist g new_gd worklist
  in
  (* Produces the "weight" of the given colorable argument *)
  let color_weight (color : arg) : int =
    (* checks if the given arg is one of the pre-defined reg colors *)
    let reg_pos = find_pos reg_colors color in
    if reg_pos != -1
    then reg_pos (* if its not a pre-defined color, it spills to stack *)
    else
      match color with
      | RegOffset (si, RBP) ->
          (* Spilled weight *)
          (Int.abs si / word_size) + max_color_weight
      | _ -> raise (InternalCompilerError "color_weight was given an argument that isn't colorable")
  in
  (* finds the minimum next color based on the given list of already generated colors *)
  let minimum_color (colors : arg list) : arg =
    (* ASSUMES that the list is sorted *)
    let rec get_min_weight cs prev_weight : int =
      match cs with
      | [] -> prev_weight + 1
      | (c, w) :: rest -> if w != prev_weight + 1 then prev_weight + 1 else get_min_weight rest w
    in
    let sorted =
      List.sort (fun (_, w1) (_, w2) -> w1 - w2) (List.map (fun c -> (c, color_weight c)) colors)
    in
    let min_weigth = get_min_weight sorted (-1) in
    (* check to either get reg color or spill to stack *)
    if min_weigth <= max_color_weight
    then List.nth reg_colors min_weigth
    else RegOffset ((min_weigth - max_color_weight) * word_size * -1, RBP)
  in
  (* Generates the environment from the given worklist, accumulates the ongoing coloring in the colored hashmap *)
  let rec color_help (worklist : string list) (colored : arg HashMap.t) : arg name_envt =
    match worklist with
    | [] -> init_env
    | node :: rest ->
        let neigh = get_neighbors g node in
        let known_colors =
          List.fold_left
            (fun prev_col n ->
              match HashMap.find_opt n colored with
              | None -> prev_col
              | Some c -> c :: prev_col )
            [] neigh
        in
        let min_color = minimum_color known_colors in
        [(node, min_color)] @ color_help rest (HashMap.add node min_color colored)
  in
  let worklist = List.rev (generate_worklist g (get_degree g) []) in
  color_help worklist Graph.empty

(* Creates a nested environment mapping closure tags to register and stack locations. *)
(* DESIGN DECISION: we chose to utilize tags instead of strings as we wouldn't need to change the anf *)
(*                  phase, and we would only need to be careful about not retagging the AST *)
let register_allocation (prog : (StringSet.t * tag) aprogram) :
    (StringSet.t * tag) aprogram * arg name_envt tag_envt =
  let rec alloc_A (a : (StringSet.t * tag) aexpr) : arg name_envt tag_envt =
    match a with
    | ALet (name, c_e, a_body, _) ->
        let c_env = alloc_C c_e in
        let a_body_env = alloc_A a_body in
        c_env @ a_body_env
    | ASeq (e1, e2, _) ->
        let c_env = alloc_C e1 in
        let a_body_env = alloc_A e2 in
        c_env @ a_body_env
    | ALetRec (binds, a_body, _) ->
        let binds_env =
          List.fold_left
            (fun prev_env (name, c_e) ->
              let c_env = alloc_C c_e in
              c_env @ prev_env )
            [] binds
        in
        let a_body_env = alloc_A a_body in
        binds_env @ a_body_env
    | ACExpr c_e -> alloc_C c_e
  and alloc_C (c : (StringSet.t * tag) cexpr) : arg name_envt tag_envt =
    match c with
    | CIf (_, a_then, a_else, _) ->
        let then_env = alloc_A a_then in
        let else_env = alloc_A a_else in
        then_env @ else_env
    | CLambda (args, body, (fvs, tag)) ->
        let arg_env = List.mapi (fun i name -> (name, RegOffset ((3 + i) * word_size, RBP))) args in
        let body_graph = interfere body fvs (StringSet.of_list args) in
        let lam_graph = pairup body_graph fvs in
        [(tag, color_graph lam_graph arg_env)] @ alloc_A body
    | _ -> []
  in
  match prog with
  | AProgram (a_body, (_, tag)) ->
      let body_env = [(tag, color_graph (interfere a_body StringSet.empty StringSet.empty) [])] in
      let prog_env = alloc_A a_body @ body_env in
      (prog, prog_env)

(* helper to align space to a multiple of 16 *)
let align_space space = Int64.of_int (space + (space mod (word_size * 2)))

(* Clears the stack with even sentinel values (0xBECCAFEDE) such that our garbage collector cannot *)
(* walk though foreign values that look like tagged-snakevals but really aren't *)
let clear_stack space =
  int_map
    (fun offset ->
      IMov
        (Sized (QWORD_PTR, RegOffset (word_size * offset, RSP)), HexConst (Int64.of_int 0xBECCAFEDE))
      )
    (space / 8) 0

(* Clears the registers used in register allocation so that garbage isn't pushed onto the stack if garbage
   collection (a native call) is tried before any SNAKEVALS are put in the registers *)
let clear_registers =
  [ILineComment "clear registers"]
  @ List.concat_map (fun reg -> [IMov (reg, HexConst (Int64.of_int 0xBECCAFEDE))]) reg_colors

let push_callee_saved_registers =
  [ILineComment "push callee save regisers"]
  @ List.concat_map (fun reg -> [IPush reg]) callee_saved_regs

let pop_callee_saved_registers =
  [ILineComment "pop callee save regisers"]
  @ List.rev (List.concat_map (fun reg -> [IPop reg]) callee_saved_regs)

let rec compile_fun
    (fun_name : string)
    (args : string list)
    (body : (StringSet.t * tag) aexpr)
    (env : arg name_envt tag_envt)
    (space : int64) : instruction list * instruction list * instruction list =
  let stack_setup =
    [ ILabel fun_name;
      IPush (Reg RBP);
      IMov (Reg RBP, Reg RSP);
      ILabel (fun_name ^ "_body");
      ISub (Reg RSP, Const space) ]
    @ clear_stack (Int64.to_int space)
  in
  let compiled_body = compile_aexpr body 0 env (List.length args) true in
  let postlude = [IAdd (Reg RSP, Const space); IPop (Reg RBP); IRet] in
  (stack_setup, compiled_body, postlude)

and compile_aexpr
    (e : (StringSet.t * tag) aexpr)
    (tag_space : tag)
    (env : arg name_envt tag_envt)
    (num_args : int)
    (is_tail : bool) : instruction list =
  match e with
  | ALet (name, c_e, a_body, _) ->
      let prelude = compile_cexpr c_e tag_space env num_args false in
      let body = compile_aexpr a_body tag_space env num_args is_tail in
      prelude @ [IMov (find_in_env_tag env name tag_space, Reg RAX)] @ body
  | ACExpr c_e -> compile_cexpr c_e tag_space env num_args is_tail
  | ASeq (e1, e2, _) ->
      let prelude = compile_cexpr e1 tag_space env num_args false in
      let body = compile_aexpr e2 tag_space env num_args is_tail in
      prelude @ body
  | ALetRec (binds, body, _) ->
      let compiled_closures, _ =
        List.fold_left
          (fun (prev_ins, offset) (name, func) ->
            let fvs_num = StringSet.cardinal (cexpr_fvs func) in
            let size = fvs_num + 3 in
            let padding = size mod 2 in
            let size = size + padding in
            let ins =
              [ IMov (Reg scratch_reg, Reg heap_reg);
                IAdd (Reg scratch_reg, Const (Int64.of_int (5 + (word_size * offset))));
                IMov (find_in_env_tag env name tag_space, Reg scratch_reg) ]
            in
            (prev_ins @ ins, offset + size) )
          ([], 0) binds
      in
      let compiled_lambdas =
        List.concat_map (fun (_, lambda) -> compile_cexpr lambda tag_space env num_args false) binds
      in
      let compiled_body = compile_aexpr body tag_space env num_args is_tail in
      compiled_closures @ compiled_lambdas @ compiled_body

and compile_cexpr (e : (StringSet.t * tag) cexpr) tag_space env num_args is_tail =
  let local_env = find env tag_space in
  let compile_checktag (imm : arg) (err_label : string) (tag : int64) (mask : int64) :
      instruction list =
    [ IMov (Reg RAX, imm);
      (* applies the mask *)
      IAnd (Reg RAX, HexConst mask);
      (* compares result to tag *)
      ICmp (Reg RAX, Const tag);
      (* moves the error in the first x64 arg reg and jumps to error label if it is zero *)
      IJne (Label err_label) ]
  in
  (* helpers for compiling different types of tags *)
  let compile_checktag_num imm err_label = compile_checktag imm err_label num_tag num_tag_mask in
  let compile_checktag_bool imm err_label = compile_checktag imm err_label bool_tag bool_tag_mask in
  let compile_checktag_tuple imm err_label =
    compile_checktag imm err_label tuple_tag tuple_tag_mask
  in
  let compile_checktag_closure imm err_label =
    compile_checktag imm err_label closure_tag closure_tag_mask
  in
  let compile_checktag_struct imm err_label =
    compile_checktag imm err_label struct_tag struct_tag_mask
  in
  (* compiles a test for checking if the value is nil *)
  let compile_check_nil (imm : arg) (err_label : string) : instruction list =
    [IMov (Reg RAX, imm); ICmp (Reg RAX, const_nil); IJz (Label err_label)]
  in
  (* compiles a jump to an overflow error *)
  let compile_check_overflow : instruction list = [IJo (Label "?err_overflow")] in
  let check_same_struct imm err struid tag =
    match struid with
    | None -> []
    | Some uid ->
        let done_check_label = sprintf "done_check_label_%d" tag in
        [IMov (Reg RAX, imm); ICmp (Reg RAX, const_nil); IJe (Label done_check_label)]
        @ compile_checktag_struct imm err
        @ [ IMov (Reg RAX, imm);
            ISub (Reg RAX, Const struct_tag);
            IMov (Reg RAX, RegOffset (0, RAX));
            ICmp (Reg RAX, Const (Int64.of_int (uid lsl 1)));
            IJne (Label "?err_setter_field_wrong_struct");
            ILabel done_check_label ]
  in
  match e with
  | CIf (imm_cond, a_then, a_else, (_, tag)) ->
      let then_label = sprintf "then_if_%d" tag in
      let else_label = sprintf "else_if_%d" tag in
      let done_label = sprintf "done_if_%d" tag in
      let cond_imm = compile_imm imm_cond local_env in
      compile_checktag_bool cond_imm "?err_if_not_bool"
      @ [IMov (Reg RAX, cond_imm)]
      @ [IMov (Reg scratch_reg, const_true)]
      @ [ICmp (Reg RAX, Reg scratch_reg)]
      @ [IJne (Label else_label); ILabel then_label]
      @ compile_aexpr a_then tag_space env num_args is_tail
      @ [IJmp (Label done_label); ILabel else_label]
      @ compile_aexpr a_else tag_space env num_args is_tail
      @ [ILabel done_label]
  | CPrim1 (op, imm_e, (_, tag)) -> (
      let e_reg = compile_imm imm_e local_env in
      (* Compiles a tag contract *)
      let compile_contract tag mask =
        [ IMov (Reg RAX, e_reg);
          (* applies the mask *)
          IAnd (Reg RAX, HexConst mask);
          (* compares result with tag *)
          ICmp (Reg RAX, Const tag);
          (* if equal, it sets AL to 1, else 0*)
          ISete (Reg AL);
          (* shifts left rax by 63 to form a boolean *)
          IShl (Reg RAX, Const 63L);
          (* moves false in temp reg *)
          IMov (Reg scratch_reg, const_false);
          (* ors rax with temp to get final boolean *)
          IOr (Reg RAX, Reg scratch_reg) ]
      in
      match op with
      | IsBool -> compile_contract bool_tag bool_tag_mask
      | IsNum -> compile_contract num_tag num_tag_mask
      | IsTuple -> compile_contract tuple_tag tuple_tag_mask
      | Add1 ->
          compile_checktag_num e_reg "?err_arith_not_num"
          @ [IMov (Reg RAX, e_reg); IAdd (Reg RAX, Const 2L)]
          @ compile_check_overflow
      | Sub1 ->
          compile_checktag_num e_reg "?err_arith_not_num"
          @ [IMov (Reg RAX, e_reg); ISub (Reg RAX, Const 2L)]
          @ compile_check_overflow
      | Not ->
          compile_checktag_bool e_reg "?err_logic_not_bool"
          @ [ IMov (Reg RAX, e_reg);
              IMov (Reg scratch_reg, bool_mask);
              IXor (Reg RAX, Reg scratch_reg) ]
      | PrintStack ->
          let saved_data, restore_data = save_regs in
          saved_data
          @ [ IMov (Reg RAX, e_reg);
              IMov (Reg RDI, Reg RAX);
              IMov (Reg RSI, Reg RBP);
              IMov (Reg RDX, Reg RSP);
              IMov (Reg RCX, Const (Int64.of_int num_args));
              ICall (Label "?print_stack") ]
          @ restore_data )
  | CPrim2 (op, left, right, (_, tag)) -> (
      let l_imm = compile_imm left local_env in
      let r_imm = compile_imm right local_env in
      (* compiles a numeric comparison. NOTE: expects a jump instruction to a label *)
      let compile_num_comp (ins : instruction) : instruction list =
        compile_checktag_num l_imm "?err_comp_not_num"
        @ compile_checktag_num r_imm "?err_comp_not_num"
        @ [ IMov (Reg RAX, l_imm);
            IMov (Reg scratch_reg, r_imm);
            ICmp (Reg RAX, Reg scratch_reg);
            IMov (Reg RAX, const_true);
            (* the given jump instruction *)
            ins;
            IMov (Reg RAX, const_false) ]
      in
      match op with
      | Plus ->
          compile_checktag_num l_imm "?err_arith_not_num"
          @ compile_checktag_num r_imm "?err_arith_not_num"
          @ [IMov (Reg RAX, l_imm); IAdd (Reg RAX, r_imm)]
          @ compile_check_overflow
      | Minus ->
          compile_checktag_num l_imm "?err_arith_not_num"
          @ compile_checktag_num r_imm "?err_arith_not_num"
          @ [IMov (Reg RAX, l_imm); ISub (Reg RAX, r_imm)]
          @ compile_check_overflow
      | Times ->
          compile_checktag_num l_imm "?err_arith_not_num"
          @ compile_checktag_num r_imm "?err_arith_not_num"
          @ [IMov (Reg RAX, l_imm); ISar (Reg RAX, Const 1L); IMul (Reg RAX, r_imm)]
          @ compile_check_overflow
      | And | Or -> raise (InternalCompilerError "Impossible: non-desugared primitive operation")
      | Greater ->
          let done_label = sprintf "done_greater_%d" tag in
          compile_num_comp (IJg (Label done_label)) @ [ILabel done_label]
      | GreaterEq ->
          let done_label = sprintf "done_greatereq_%d" tag in
          compile_num_comp (IJge (Label done_label)) @ [ILabel done_label]
      | Less ->
          let done_label = sprintf "done_less_%d" tag in
          compile_num_comp (IJl (Label done_label)) @ [ILabel done_label]
      | LessEq ->
          let done_label = sprintf "done_lesseq_%d" tag in
          compile_num_comp (IJle (Label done_label)) @ [ILabel done_label]
      | Eq ->
          let done_label = sprintf "done_eq_%d" tag in
          [ IMov (Reg RAX, l_imm);
            IMov (Reg scratch_reg, r_imm);
            ICmp (Reg RAX, Reg scratch_reg);
            IMov (Reg RAX, const_true);
            IJe (Label done_label);
            IMov (Reg RAX, const_false);
            ILabel done_label ]
      | CheckSize ->
          let size =
            match right with
            | ImmNum (n, _) -> Int64.of_int (Int64.to_int n lsl 1)
            | _ -> raise (InternalCompilerError "CheckSize rhs wasn't a number")
          in
          let compiled_tup = l_imm in
          (* Throw err_TUPLE_BAD_DESTRUCT since this value was originally from a desugared tuple binding *)
          compile_check_nil compiled_tup "?err_tuple_bad_destruct"
          @ compile_checktag_tuple compiled_tup "?err_tuple_bad_destruct"
          @ [ IMov (Reg RAX, compiled_tup);
              ISub (Reg RAX, Const tuple_tag);
              IMov (Reg scratch_reg, Const size);
              (* check if sizes match *)
              ICmp (Reg scratch_reg, RegOffset (0, RAX));
              IJne (Label "?err_tuple_bad_destruct") ] )
  | CLambda (args, body, (fvs, tag)) ->
      let lambda_label = sprintf "lambda_%d" tag in
      let lambda_end_label = sprintf "lambda_end_%d" tag in
      let lam_env = find env tag in
      let arity = List.length args in
      let fvs = List.sort compare (StringSet.elements fvs) in
      let fvs_num = List.length fvs in
      (* allocates the needed amount of space based on the free variables. *)
      (* NOTE: only allocates fvs spilled to the stack *)
      let fvs_space =
        List.fold_left
          (fun prev fv ->
            match find lam_env fv with
            | RegOffset (_, RBP) -> prev + word_size
            | _ -> prev )
          0 fvs
      in
      let compiled_fvs, _ =
        List.fold_right
          (fun name (prev_args, i) ->
            ( prev_args
              @ [ IInstrComment
                    ( IMov (Reg RAX, RegOffset ((i + 3) * word_size, scratch_reg)),
                      sprintf "load fv: %s" name );
                  IMov (find lam_env name, Reg RAX) ],
              i + 1 ) )
          fvs ([], 0)
      in
      let local_var_space = deepest_stack lam_env * word_size in
      let compiled_closure_vars, _ =
        List.fold_right
          (fun name (prev_args, i) ->
            ( prev_args
              @ [ IInstrComment (IMov (Reg RAX, find local_env name), sprintf "pack fv: %s" name);
                  IMov (RegOffset (i * word_size, heap_reg), Reg RAX) ],
              i + 1 ) )
          fvs ([], 3)
      in
      let compiled_body = compile_aexpr body tag env arity is_tail in
      let stack_space = Int64.of_int (fvs_space + local_var_space) in
      let size = align_space ((3 + fvs_num) * word_size) in
      [ IJmp (Label lambda_end_label);
        ILabel lambda_label;
        IPush (Reg RBP);
        ILineComment (sprintf "fvs space: %d" fvs_space);
        ILineComment (sprintf "local var space: %d" local_var_space);
        IMov (Reg RBP, Reg RSP);
        ISub (Reg RSP, Const stack_space) ]
      @ clear_stack (Int64.to_int stack_space)
      @ [ IMov (Reg scratch_reg, RegOffset (2 * word_size, RBP));
          ISub (Reg scratch_reg, HexConst closure_tag) ]
      @ compiled_fvs @ compiled_body
      @ [IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet; ILabel lambda_end_label]
      @ reserve (Int64.to_int size) tag
      @ [ IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (arity lsl 1)));
          IMov (Reg scratch_reg, Label lambda_label);
          IMov (Sized (QWORD_PTR, RegOffset (word_size, heap_reg)), Reg scratch_reg);
          IMov
            ( Sized (QWORD_PTR, RegOffset (word_size * 2, heap_reg)),
              Const (Int64.of_int (fvs_num lsl 1)) );
          ILineComment (sprintf "free vars: %d" fvs_num) ]
      @ compiled_closure_vars
      @ [ IMov (Reg RAX, Reg heap_reg);
          IAdd (Reg RAX, HexConst closure_tag);
          IAdd (Reg heap_reg, Const size) ]
  | CApp (ImmId (funname, _), imm_args, Native, _) ->
      let compiled_args = List.map (fun a -> compile_imm a local_env) imm_args in
      native_call (Label ("?" ^ funname)) compiled_args
  | CApp (func, imm_args, cl, _) ->
      let compiled_func = compile_imm func local_env in
      let compiled_args = List.map (fun a -> compile_imm a local_env) imm_args in
      let saved_data, restore_data = save_regs in
      let arity = List.length imm_args in
      let arg_space = (arity + 1) * word_size in
      let pushed_args =
        List.concat_map
          (fun a -> [IMov (Reg scratch_reg, a); IPush (Reg scratch_reg)])
          (List.rev compiled_args)
        @ [IPush (Sized (QWORD_PTR, compiled_func))]
      in
      compile_checktag_closure compiled_func "?err_call_not_closure"
      @ [ IMov (Reg RAX, compiled_func);
          ISub (Reg RAX, HexConst closure_tag);
          IMov (Reg scratch_reg, RegOffset (0, RAX));
          ICmp (Reg scratch_reg, Const (Int64.of_int (arity lsl 1)));
          IJne (Label "?err_call_arity_err") ]
      @ saved_data @ pushed_args
      @ [ICall (RegOffset (8, RAX)); IAdd (Reg RSP, Const (Int64.of_int arg_space))]
      @ restore_data
  | CTuple (elems, (_, tag)) ->
      let num_elems = List.length elems in
      let elem_ins =
        List.concat
          (List.mapi
             (fun i el ->
               [ IMov (Reg scratch_reg, compile_imm el local_env);
                 IMov (Sized (QWORD_PTR, RegOffset ((i + 1) * word_size, heap_reg)), Reg scratch_reg)
               ] )
             elems )
      in
      let padding = if num_elems mod 2 == 0 then word_size * 2 else word_size in
      let size = (num_elems * word_size) + padding in
      reserve size tag
      @ [ IMov (Reg RAX, Reg heap_reg);
          IOr (Reg RAX, Const tuple_tag);
          IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (num_elems lsl 1)))
        ]
      @ elem_ins
      @ [IAdd (Reg heap_reg, Const (Int64.of_int size))]
  | CGetItem (imm_tup, imm_i, _) ->
      let compiled_tup = compile_imm imm_tup local_env in
      let compiled_i = compile_imm imm_i local_env in
      compile_check_nil compiled_tup "?err_nil_deref"
      @ compile_checktag_tuple compiled_tup "?err_get_not_tuple"
      @ compile_checktag_num compiled_i "?err_get_not_num"
      @ [ IMov (Reg RAX, compiled_tup);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg scratch_reg, compiled_i);
          (* index bound checking *)
          IAdd (Reg scratch_reg, Const 2L);
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJg (Label "?err_get_high_index");
          ICmp (Reg scratch_reg, Const 2L);
          IJl (Label "?err_get_low_index");
          (* convert to machine number *)
          ISub (Reg scratch_reg, Const 2L);
          ISar (Reg scratch_reg, Const 1L);
          IAdd (Reg scratch_reg, Const 1L);
          (* multiply by 8 to shift by word size *)
          IShl (Reg scratch_reg, Const 3L);
          (* shift pointer by index amount *)
          IAdd (Reg RAX, Reg scratch_reg);
          (* dereference rax (which has the addr) into rax *)
          IMov (Reg RAX, RegOffset (0, RAX)) ]
  | CSetItem (imm_tup, imm_i, imm_new, _) ->
      let compiled_tup = compile_imm imm_tup local_env in
      let compiled_i = compile_imm imm_i local_env in
      let compiled_new = compile_imm imm_new local_env in
      compile_check_nil compiled_tup "?err_nil_deref"
      @ compile_checktag_tuple compiled_tup "?err_set_not_tuple"
      @ compile_checktag_num compiled_i "?err_set_not_num"
      @ [ IMov (Reg RAX, compiled_tup);
          ISub (Reg RAX, Const tuple_tag);
          IMov (Reg scratch_reg, compiled_i);
          (* index bound checking *)
          IAdd (Reg scratch_reg, Const 2L);
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJg (Label "?err_set_high_index");
          ICmp (Reg scratch_reg, Const 2L);
          IJl (Label "?err_set_low_index");
          (* convert to machine number *)
          ISub (Reg scratch_reg, Const 2L);
          ISar (Reg scratch_reg, Const 1L);
          IAdd (Reg scratch_reg, Const 1L);
          (* multiply by 8 to shift by word size *)
          IShl (Reg scratch_reg, Const 3L);
          (* shift pointer by index amount *)
          IAdd (Reg RAX, Reg scratch_reg);
          (* modify pointer of rax to new arg *)
          IMov (Reg scratch_reg, compiled_new);
          IMov (RegOffset (0, RAX), Reg scratch_reg);
          (* dereference rax (which has the new val addr) into rax *)
          IMov (Reg RAX, RegOffset (0, RAX)) ]
  | CConstruct (stag, fields, (_, tag)) ->
      let num_fields = List.length fields in
      let fields_ins, _ =
        List.fold_left2
          (fun (prev_ins, i) el maybe_fid ->
            let c_el = compile_imm el local_env in
            let ins =
              [IMov (Reg scratch_reg, Reg RAX)]
              @ check_same_struct c_el "?err_construct_field_wrong_struct" maybe_fid
                  (immexpr_info el (fun (_, t) -> t))
              @ [ IMov (Reg RAX, Reg scratch_reg);
                  IMov (Reg scratch_reg, c_el);
                  IMov
                    (Sized (QWORD_PTR, RegOffset ((i + 2) * word_size, heap_reg)), Reg scratch_reg)
                ]
            in
            (prev_ins @ ins, i + 1) )
          ([], 0) fields stag.field_uids
      in
      let padding = if num_fields mod 2 == 0 then word_size * 2 else word_size * 3 in
      let size = (num_fields * word_size) + padding in
      reserve size tag
      @ [ IMov (Reg RAX, Reg heap_reg);
          IOr (Reg RAX, Const struct_tag);
          IMov (Sized (QWORD_PTR, RegOffset (0, heap_reg)), Const (Int64.of_int (stag.uid lsl 1)));
          IMov
            ( Sized (QWORD_PTR, RegOffset (word_size, heap_reg)),
              Const (Int64.of_int (num_fields lsl 1)) ) ]
      @ fields_ins
      @ [IAdd (Reg heap_reg, Const (Int64.of_int size))]
  | CGetter (imm_s, ftag, (_, tag)) ->
      let c_imm = compile_imm imm_s local_env in
      compile_checktag_struct c_imm "?err_getter_not_struct"
      @ [ IMov (Reg RAX, c_imm);
          ISub (Reg RAX, Const struct_tag);
          (* field bound checking *)
          IMov (Reg scratch_reg, Const (Int64.of_int (ftag.uid lsl 1)));
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJne (Label "?err_getter_field_not_found");
          IMov (Reg scratch_reg, Const (Int64.of_int ((ftag.offset - 2) lsl 1)));
          ICmp (Reg scratch_reg, RegOffset (word_size, RAX));
          IJg (Label "?err_getter_field_not_found");
          ICmp (Reg scratch_reg, Const (Int64.of_int 0));
          IJl (Label "?err_getter_field_not_found");
          (* multiply by 4 to shift by word size *)
          IMov (Reg scratch_reg, Const (Int64.of_int (ftag.offset * word_size)));
          (* shift pointer by index amount *)
          IAdd (Reg RAX, Reg scratch_reg);
          (* dereference rax (which has the addr) into rax *)
          IMov (Reg RAX, RegOffset (0, RAX)) ]
  | CSetter (imm_s, ftag, imm_new_field, (_, tag)) ->
      let c_imm = compile_imm imm_s local_env in
      let c_new_field = compile_imm imm_new_field local_env in
      compile_checktag_struct c_imm "?err_setter_not_struct"
      @ [ IMov (Reg RAX, c_imm);
          ISub (Reg RAX, Const struct_tag);
          (* field bound checking *)
          IMov (Reg scratch_reg, Const (Int64.of_int (ftag.uid lsl 1)));
          ICmp (Reg scratch_reg, RegOffset (0, RAX));
          IJne (Label "?err_setter_field_not_found");
          IMov (Reg scratch_reg, Const (Int64.of_int ((ftag.offset - 2) lsl 1)));
          ICmp (Reg scratch_reg, RegOffset (word_size, RAX));
          IJg (Label "?err_setter_field_not_found");
          ICmp (Reg scratch_reg, Const (Int64.of_int 0));
          IJl (Label "?err_setter_field_not_found");
          (* multiply by 4 to shift by word size *)
          IMov (Reg scratch_reg, Const (Int64.of_int (ftag.offset * word_size))) ]
      @ check_same_struct c_new_field "?err_setter_field_wrong_struct" ftag.field_uid tag
      @ [ (* restore struct *)
          IMov (Reg RAX, c_imm);
          ISub (Reg RAX, Const struct_tag);
          (* shift pointer by index amount *)
          IAdd (Reg RAX, Reg scratch_reg);
          (* mutate field *)
          IMov (Reg scratch_reg, c_new_field);
          IMov (RegOffset (0, RAX), Reg scratch_reg);
          (* dereference rax (which has the addr) into rax *)
          IMov (Reg RAX, RegOffset (0, RAX)) ]
  | CIs (imm_s, stag, (_, tag)) ->
      let c_imm = compile_imm imm_s local_env in
      let is_struct_label = sprintf "checkstruct_is_%d" tag in
      let done_label = sprintf "done_is_%d" tag in
      let ret_bool_label = sprintf "retbool_is_%d" tag in
      (* first, we check if the given value is a struct. *)
      [ IMov (Reg RAX, c_imm);
        (* applies the mask *)
        IAnd (Reg RAX, HexConst struct_tag_mask);
        (* compares result with tag *)
        ICmp (Reg RAX, Const struct_tag);
        IJe (Label is_struct_label);
        ILabel ret_bool_label;
        (* if equal, it sets AL to 1, else 0*)
        ISete (Reg AL);
        (* shifts left rax by 63 to form a boolean *)
        IShl (Reg RAX, Const 63L);
        (* moves false in temp reg *)
        IMov (Reg scratch_reg, const_false);
        (* ors rax with temp to get final boolean *)
        IOr (Reg RAX, Reg scratch_reg);
        (* jump out *)
        IJmp (Label done_label);
        ILabel is_struct_label;
        (* now, we check if the unique ids are the same *)
        IMov (Reg RAX, c_imm);
        (* untag struct *)
        ISub (Reg RAX, Const struct_tag);
        (* deref rax *)
        IMov (Reg RAX, RegOffset (0, RAX));
        (* compare with unique tag *)
        ICmp (Reg RAX, Const (Int64.of_int (stag.uid lsl 1)));
        (* jump to bool ret *)
        IJmp (Label ret_bool_label);
        ILabel done_label ]
  | CImmExpr imm_e -> [IMov (Reg RAX, compile_imm imm_e local_env)]

and compile_imm e (env : arg name_envt) =
  match e with
  | ImmNum (n, _) -> Const (Int64.shift_left n 1)
  | ImmBool (true, _) -> const_true
  | ImmBool (false, _) -> const_false
  | ImmId (x, _) -> find env x
  | ImmNil _ -> const_nil

and reserve (size : int) tag =
  let ok = sprintf "$memcheck_%d" tag in
  [ ILineComment (sprintf "Reserving %d words" (size / word_size));
    ICall (Label "?get_heap_end");
    ISub (Reg RAX, Const (Int64.of_int size));
    ICmp (Reg RAX, Reg heap_reg);
    IJge (Label ok) ]
  @ native_call (Label "?try_gc")
      [ (* alloc_ptr in C *)
        Sized (QWORD_PTR, Reg heap_reg);
        (* bytes_needed in C *)
        Sized (QWORD_PTR, Const (Int64.of_int size));
        (* first_frame in C *)
        Sized (QWORD_PTR, Reg RBP);
        (* stack_top in C *)
        Sized (QWORD_PTR, Reg RSP) ]
  @ [ IInstrComment
        ( IMov (Reg heap_reg, Reg RAX),
          "assume gc success if returning here, so RAX holds the new heap_reg value" );
      ILabel ok ]

and args_help args regs =
  match (args, regs) with
  | arg :: args, reg :: regs -> IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and save_regs =
  let saved_data = List.map (fun r -> IPush r) reg_colors in
  let restore_data = List.map (fun r -> IPop r) (List.rev reg_colors) in
  (saved_data, restore_data)

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let arity = List.length args in
  let arg_ins =
    List.concat
      (List.rev
         (List.mapi
            (fun i a ->
              if i < 6
              then [IMov (Reg RAX, a); IMov (Reg (List.nth first_six_args_registers i), Reg RAX)]
              else [IMov (Reg RAX, a); IPush (Reg RAX)] )
            args ) )
  in
  let saved_data, restore_data = save_regs in
  let groom_stack =
    if arity > 6 then [IAdd (Reg RSP, Const (Int64.of_int (word_size * (arity - 6))))] else []
  in
  saved_data @ arg_ins @ [ICall label] @ groom_stack @ restore_data

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let setup =
    List.rev_map
      (fun arg ->
        match arg with
        | Sized _ -> IPush arg
        | _ -> IPush (Sized (DWORD_PTR, arg)) )
      args
  in
  let teardown =
    let len = List.length args in
    if len = 0
    then []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * len))),
            sprintf "Popping %d arguments" len ) ]
  in
  setup @ [ICall closure] @ teardown

(* This function can be used to take the native functions and produce Lambdas whose bodies
   simply contain an EApp (with a Native call_type) to that native function. *)
let add_native_lambdas (p : sourcespan program) : sourcespan program =
  let help prog_body =
    let info = dummy_span in
    let bindings =
      List.map
        (fun (name, arity) ->
          let binds = int_map (fun i -> BName (sprintf "a_%d" i, false, info)) arity 0 in
          let ids = int_map (fun i -> EId (sprintf "a_%d" i, info)) arity 0 in
          let func_id = EId (name, info) in
          (BName (name, false, info), ELambda (binds, EApp (func_id, ids, Native, info), info), info)
          )
        wrappable_native_fun_env
    in
    ELetRec (bindings, prog_body, info)
  in
  match p with
  | Program (strus, declss, body, tag) -> Program (strus, declss, help body, tag)

let compile_prog ((anfed : (StringSet.t * tag) aprogram), (env : arg name_envt tag_envt)) =
  let prelude =
    "section .text\n\
     extern ?error\n\
     extern ?input\n\
     extern ?print\n\
     extern ?print_stack\n\
     extern ?equal\n\
     extern ?testarg\n\
     extern ?try_gc\n\
     extern ?naive_print_heap\n\
     extern ?HEAP\n\
     extern ?HEAP_END\n\
     extern ?set_stack_bottom\n\
     extern ?get_heap_end\n\
     global ?our_code_starts_here"
  in
  let suffix =
    sprintf
      "\n\
       ?err_comp_not_num:%s\n\
       ?err_arith_not_num:%s\n\
       ?err_logic_not_bool:%s\n\
       ?err_if_not_bool:%s\n\
       ?err_overflow:%s\n\
       ?err_get_not_tuple:%s\n\
       ?err_get_low_index:%s\n\
       ?err_get_high_index:%s\n\
       ?err_nil_deref:%s\n\
       ?err_out_of_memory:%s\n\
       ?err_set_not_tuple:%s\n\
       ?err_set_low_index:%s\n\
       ?err_set_high_index:%s\n\
       ?err_call_not_closure:%s\n\
       ?err_call_arity_err:%s\n\
       ?err_set_not_num:%s\n\
       ?err_get_not_num:%s\n\
       ?err_tuple_bad_destruct:%s\n\
       ?err_getter_not_struct:%s\n\
       ?err_setter_not_struct:%s\n\
       ?err_getter_field_not_found:%s\n\
       ?err_setter_field_not_found:%s\n\
       ?err_setter_field_wrong_struct:%s\n\
       ?err_construct_field_wrong_struct:%s\n"
      (to_asm (native_call (Label "?error") [Const err_COMP_NOT_NUM; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_ARITH_NOT_NUM; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_LOGIC_NOT_BOOL; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_IF_NOT_BOOL; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_OVERFLOW; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GET_NOT_TUPLE; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GET_LOW_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_GET_HIGH_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_NIL_DEREF; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_OUT_OF_MEMORY; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_NOT_TUPLE; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_SET_LOW_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_HIGH_INDEX; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_CALL_NOT_CLOSURE; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_CALL_ARITY_ERR; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SET_NOT_NUM; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GET_NOT_NUM; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_TUPLE_BAD_DESTRUCT; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GETTER_NOT_STRUCT; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_SETTER_NOT_STRUCT; Reg RAX]))
      (to_asm (native_call (Label "?error") [Const err_GETTER_FIELD_NOT_FOUND; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SETTER_FIELD_NOT_FOUND; Reg scratch_reg]))
      (to_asm (native_call (Label "?error") [Const err_SETTER_FIELD_WRONG_STRUCT; Reg scratch_reg]))
      (to_asm
         (native_call (Label "?error") [Const err_CONSTRUCT_FIELD_WRONG_STRUCT; Reg scratch_reg]) )
  in
  match anfed with
  | AProgram (body, (_, tag)) ->
      let reserve_space = deepest_stack (find env tag) * word_size in
      (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
      let prologue, comp_main, epilogue =
        compile_fun "?our_code_starts_here" ["$heap"; "$size"] body env (align_space reserve_space)
      in
      let heap_start =
        [ ILineComment "heap start";
          IInstrComment
            ( IMov (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0)),
              "Load heap_reg with our argument, the heap pointer" );
          IInstrComment
            ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L),
              "Align it to the nearest multiple of 16" );
          IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L);
          IInstrComment
            ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg),
              "by adding no more than 15 to it" );
          ILineComment "setting base stack pointer";
          IMov (Reg RDI, Reg RBP);
          ICall (Label "?set_stack_bottom") ]
      in
      let main =
        prologue @ push_callee_saved_registers @ heap_start @ clear_registers @ comp_main
        @ pop_callee_saved_registers @ epilogue
      in
      sprintf "%s%s%s\n" prelude (to_asm main) suffix

let run_if should_run f = if should_run then f else no_op_phase

let pick_alloc_strategy (strat : alloc_strategy) =
  match strat with
  | Naive -> naive_stack_allocation
  | Register -> register_allocation

(* Disables formating for keeping pipes aligned. *)
[@@@ocamlformat "disable=true"]

let compile_to_string
    ?(no_builtins = false)
    (alloc_strat : alloc_strategy)
    (prog : sourcespan program pipeline) : string pipeline =
  prog
  |> add_err_phase well_formed is_well_formed
  |> add_phase desugared desugar 
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase tagged tag 
  |> add_phase renamed rename_and_tag
  |> add_phase structtable gensymtbl
  |> add_phase anfed (fun (p, tbl) -> atag (anf p tbl))
  |> add_phase free_vared free_vars_cache
  |> add_phase locate_bindings (pick_alloc_strategy alloc_strat)
  |> add_phase result compile_prog
