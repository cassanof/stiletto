open Printf
module StringSet = Set.Make (String)

let show_debug_print = ref false

let debug_printf fmt = if !show_debug_print then printf fmt else ifprintf stdout fmt

type tag = int

type sourcespan = Lexing.position * Lexing.position

type prim1 =
  | Add1
  | Sub1
  | IsBool
  | IsNum
  | IsTuple
  | Not
  | PrintStack

type prim2 =
  | Plus
  | Minus
  | Times
  | And
  | Or
  | Greater
  | GreaterEq
  | Less
  | LessEq
  | Eq
  | CheckSize

and 'a bind =
  | BBlank of 'a
  | BName of string * bool * 'a (* bind name * shadow * tag *)
  | BStruct of string * string * 'a (* bind name * struct name * tag *)
  | BTuple of 'a bind list * 'a

and 'a binding = 'a bind * 'a expr * 'a

and call_type =
  | Native
  | Snake
  | Prim
  | Unknown

and 'a expr =
  | ESeq of 'a expr * 'a expr * 'a
  | ETuple of 'a expr list * 'a
  | EGetItem of 'a expr * 'a expr * 'a
  | ESetItem of 'a expr * 'a expr * 'a expr * 'a
  | EConstruct of string * 'a expr list * 'a
  | EGetter of 'a expr * string * 'a
  | ESetter of 'a expr * string * 'a expr * 'a
  | EAs of 'a expr * string * 'a
  | EIs of 'a expr * string * 'a
  | ELet of 'a binding list * 'a expr * 'a
  | EPrim1 of prim1 * 'a expr * 'a
  | EPrim2 of prim2 * 'a expr * 'a expr * 'a
  | EIf of 'a expr * 'a expr * 'a expr * 'a
  | ENumber of int64 * 'a
  | EBool of bool * 'a
  | ENil of 'a
  | EId of string * 'a
  | EApp of 'a expr * 'a expr list * call_type * 'a
  | ELambda of 'a bind list * 'a expr * 'a
  | ELetRec of 'a binding list * 'a expr * 'a

type 'a decl = DFun of string * 'a bind list * 'a expr * 'a

type 'a strufield =
  | FName of string
  (*            id      struct name     *)
  | FStruct of string * string
  (* NOTE: can only be created internally.*)
  (*            name     bindings   body *)
  | FMethod of string * 'a bind list * 'a expr

type 'a mthd = DMethod of string * 'a bind list * 'a expr * 'a

type 'a stru = DStruct of string * 'a strufield list * 'a mthd list * 'a

type 'a program = Program of 'a stru list * 'a decl list list * 'a expr * 'a

(* the unique id for each struct *)
type stru_id = int

(* the offset of a field in a struct (in words) - fields start at word 2 *)
type field_offset = int

(* represents a tag for a struct *)
type stru_tag =
  { (* the unique id for this struct *)
    uid: stru_id;
    (* the possible unique ids for each field (a field has one if it is a struct) *)
    field_uids: stru_id option list }

(* represents a tag for a field of a struct *)
type stru_field_tag =
  { (* the memory offset where the field is *)
    offset: field_offset;
    (* the unique id of the struct that we are indexing *)
    uid: stru_id;
    (* the possible unique id of the field that exists already (a field has one if it is a struct ) *)
    field_uid: stru_id option }

(* represents a binding in the type environment, to distinguish between fields and ids *)
type strubind =
  | SBField of string
  | SBId of string

(* represents a type in the type environment. *)
type strutype =
  (* a type unrelated to structs *)
  | STNone
  (* a struct type, with the name of that struct *)
  | STSome of string
  (* a lambda type, with its bindings declared types, body and closed-over environment *)
  | STClos of (string * strutype) list * tag expr * styenv
  (* a tuple type, where the tuple has some elements of the given struct *)
  | STTup of strutype

(* represents an environment that maps bindings to struct types *)
and styenv = (strubind * strutype) list

type 'a immexpr =
  (* immediate expressions *)
  | ImmNum of int64 * 'a
  | ImmBool of bool * 'a
  | ImmId of string * 'a
  | ImmNil of 'a

and 'a cexpr =
  (* compound expressions *)
  | CIf of 'a immexpr * 'a aexpr * 'a aexpr * 'a
  | CPrim1 of prim1 * 'a immexpr * 'a
  | CPrim2 of prim2 * 'a immexpr * 'a immexpr * 'a
  | CApp of 'a immexpr * 'a immexpr list * call_type * 'a
  | CImmExpr of 'a immexpr (* for when you just need an immediate value *)
  | CConstruct of stru_tag * 'a immexpr list * 'a
  | CGetter of 'a immexpr * stru_field_tag * 'a
  | CSetter of 'a immexpr * stru_field_tag * 'a immexpr * 'a
  | CIs of 'a immexpr * stru_tag * 'a
  | CTuple of 'a immexpr list * 'a
  | CGetItem of 'a immexpr * 'a immexpr * 'a
  | CSetItem of 'a immexpr * 'a immexpr * 'a immexpr * 'a
  | CLambda of string list * 'a aexpr * 'a

and 'a aexpr =
  (* anf expressions *)
  | ASeq of 'a cexpr * 'a aexpr * 'a
  | ALet of string * 'a cexpr * 'a aexpr * 'a
  | ALetRec of (string * 'a cexpr) list * 'a aexpr * 'a
  | ACExpr of 'a cexpr

and 'a aprogram = AProgram of 'a aexpr * 'a

type alloc_strategy =
  | Register
  | Naive

let map_opt f v =
  match v with
  | None -> None
  | Some v -> Some (f v)

let get_tag_E e =
  match e with
  | ELet (_, _, t) -> t
  | EConstruct (_, _, x) -> x
  | EGetter (_, _, x) -> x
  | ESetter (_, _, _, x) -> x
  | EIs (_, _, x) -> x
  | EAs (_, _, x) -> x
  | ELetRec (_, _, t) -> t
  | EPrim1 (_, _, t) -> t
  | EPrim2 (_, _, _, t) -> t
  | EIf (_, _, _, t) -> t
  | ENil t -> t
  | ENumber (_, t) -> t
  | EBool (_, t) -> t
  | EId (_, t) -> t
  | EApp (_, _, _, t) -> t
  | ETuple (_, t) -> t
  | EGetItem (_, _, t) -> t
  | ESetItem (_, _, _, t) -> t
  | ESeq (_, _, t) -> t
  | ELambda (_, _, t) -> t

let get_tag_D d =
  match d with
  | DFun (_, _, _, t) -> t

let rec map_tag_E (f : 'a -> 'b) (e : 'a expr) =
  match e with
  | ESeq (e1, e2, a) -> ESeq (map_tag_E f e1, map_tag_E f e2, f a)
  | ETuple (exprs, a) -> ETuple (List.map (map_tag_E f) exprs, f a)
  | EConstruct (stru_name, fields, a) -> EConstruct (stru_name, List.map (map_tag_E f) fields, f a)
  | EGetter (expr, field, a) -> EGetter (map_tag_E f expr, field, f a)
  | ESetter (expr, field, new_expr, a) ->
      ESetter (map_tag_E f expr, field, map_tag_E f new_expr, f a)
  | EIs (e, stru_name, a) -> EIs (map_tag_E f e, stru_name, f a)
  | EAs (e, stru_name, a) -> EAs (map_tag_E f e, stru_name, f a)
  | EGetItem (e, idx, a) -> EGetItem (map_tag_E f e, map_tag_E f idx, f a)
  | ESetItem (e, idx, newval, a) ->
      ESetItem (map_tag_E f e, map_tag_E f idx, map_tag_E f newval, f a)
  | EId (x, a) -> EId (x, f a)
  | ENumber (n, a) -> ENumber (n, f a)
  | EBool (b, a) -> EBool (b, f a)
  | ENil a -> ENil (f a)
  | EPrim1 (op, e, a) ->
      let tag_prim = f a in
      EPrim1 (op, map_tag_E f e, tag_prim)
  | EPrim2 (op, e1, e2, a) ->
      let tag_prim = f a in
      let tag_e1 = map_tag_E f e1 in
      let tag_e2 = map_tag_E f e2 in
      EPrim2 (op, tag_e1, tag_e2, tag_prim)
  | ELet (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELet (tag_binds, tag_body, tag_let)
  | ELetRec (binds, body, a) ->
      let tag_let = f a in
      let tag_binding (b, e, t) =
        let tag_bind = f t in
        let tag_b = map_tag_B f b in
        let tag_e = map_tag_E f e in
        (tag_b, tag_e, tag_bind)
      in
      let tag_binds = List.map tag_binding binds in
      let tag_body = map_tag_E f body in
      ELetRec (tag_binds, tag_body, tag_let)
  | EIf (cond, thn, els, a) ->
      let tag_if = f a in
      let tag_cond = map_tag_E f cond in
      let tag_thn = map_tag_E f thn in
      let tag_els = map_tag_E f els in
      EIf (tag_cond, tag_thn, tag_els, tag_if)
  | EApp (func, args, native, a) ->
      let tag_app = f a in
      EApp (map_tag_E f func, List.map (map_tag_E f) args, native, tag_app)
  | ELambda (binds, body, a) ->
      let tag_lam = f a in
      ELambda (List.map (map_tag_B f) binds, map_tag_E f body, tag_lam)

and map_tag_B (f : 'a -> 'b) b =
  match b with
  | BBlank tag -> BBlank (f tag)
  | BName (x, allow_shadow, ax) ->
      let tag_ax = f ax in
      BName (x, allow_shadow, tag_ax)
  | BStruct (id, stru_name, a) -> BStruct (id, stru_name, f a)
  | BTuple (binds, t) ->
      let tag_tup = f t in
      BTuple (List.map (map_tag_B f) binds, tag_tup)

and map_tag_D (f : 'a -> 'b) d =
  match d with
  | DFun (name, args, body, a) ->
      let tag_fun = f a in
      let tag_args = List.map (map_tag_B f) args in
      let tag_body = map_tag_E f body in
      DFun (name, tag_args, tag_body, tag_fun)

and map_tag_S (f : 'a -> 'b) s =
  match s with
  | DStruct (name, fields, methods, a) ->
      DStruct (name, List.map (map_tag_F f) fields, List.map (map_tag_M f) methods, f a)

and map_tag_F (f : 'a -> 'b) fi =
  match fi with
  | FName name -> FName name
  | FStruct (name, struname) -> FStruct (name, struname)
  | FMethod (name, binds, body) -> FMethod (name, List.map (map_tag_B f) binds, map_tag_E f body)

and map_tag_M (f : 'a -> 'b) m =
  match m with
  | DMethod (name, binds, body, a) ->
      let tag_fun = f a in
      let tag_args = List.map (map_tag_B f) binds in
      let tag_body = map_tag_E f body in
      DMethod (name, tag_args, tag_body, tag_fun)

and map_tag_P (f : 'a -> 'b) p =
  match p with
  | Program (strus, declgroups, body, a) ->
      let tag_a = f a in
      let tag_stru = List.map (fun s -> map_tag_S f s) strus in
      let tag_decls = List.map (fun group -> List.map (map_tag_D f) group) declgroups in
      let tag_body = map_tag_E f body in
      Program (tag_stru, tag_decls, tag_body, tag_a)

let tag (p : 'a program) : tag program =
  let next = ref 0 in
  let tag _ =
    next := !next + 1;
    !next
  in
  map_tag_P tag p

let rec untagP (p : 'a program) : unit program =
  match p with
  | Program (strus, decls, body, _) ->
      Program
        (List.map untagS strus, List.map (fun group -> List.map untagD group) decls, untagE body, ())

and untagS s =
  match s with
  | DStruct (name, fields, methods, _) ->
      DStruct (name, List.map untagF fields, List.map untagM methods, ())

and untagF f =
  match f with
  | FName name -> FName name
  | FStruct (name, stru) -> FStruct (name, stru)
  | FMethod (name, binds, body) -> FMethod (name, List.map untagB binds, untagE body)

and untagM m =
  match m with
  | DMethod (name, args, body, _) -> DMethod (name, List.map untagB args, untagE body, ())

and untagE e =
  match e with
  | ESeq (e1, e2, _) -> ESeq (untagE e1, untagE e2, ())
  | ETuple (exprs, _) -> ETuple (List.map untagE exprs, ())
  | EConstruct (stru_name, fields, _) -> EConstruct (stru_name, List.map untagE fields, ())
  | EGetter (expr, field, _) -> EGetter (untagE expr, field, ())
  | ESetter (expr, field, new_expr, _) -> ESetter (untagE expr, field, untagE new_expr, ())
  | EIs (e, stru_name, _) -> EIs (untagE e, stru_name, ())
  | EAs (e, stru_name, _) -> EAs (untagE e, stru_name, ())
  | EGetItem (e, idx, _) -> EGetItem (untagE e, untagE idx, ())
  | ESetItem (e, idx, newval, _) -> ESetItem (untagE e, untagE idx, untagE newval, ())
  | EId (x, _) -> EId (x, ())
  | ENumber (n, _) -> ENumber (n, ())
  | EBool (b, _) -> EBool (b, ())
  | ENil _ -> ENil ()
  | EPrim1 (op, e, _) -> EPrim1 (op, untagE e, ())
  | EPrim2 (op, e1, e2, _) -> EPrim2 (op, untagE e1, untagE e2, ())
  | ELet (binds, body, _) ->
      ELet (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | EIf (cond, thn, els, _) -> EIf (untagE cond, untagE thn, untagE els, ())
  | EApp (func, args, native, _) -> EApp (untagE func, List.map untagE args, native, ())
  | ELetRec (binds, body, _) ->
      ELetRec (List.map (fun (b, e, _) -> (untagB b, untagE e, ())) binds, untagE body, ())
  | ELambda (binds, body, _) -> ELambda (List.map untagB binds, untagE body, ())

and untagB b =
  match b with
  | BBlank _ -> BBlank ()
  | BName (x, allow_shadow, _) -> BName (x, allow_shadow, ())
  | BStruct (id, stru_name, _) -> BStruct (id, stru_name, ())
  | BTuple (binds, _) -> BTuple (List.map untagB binds, ())

and untagD d =
  match d with
  | DFun (name, args, body, _) -> DFun (name, List.map untagB args, untagE body, ())

let rec untagAP (p : 'a aprogram) : unit aprogram =
  match p with
  | AProgram (body, _) -> AProgram (untagAA body, ())

and untagAA (a : 'a aexpr) : unit aexpr =
  match a with
  | ASeq (e1, e2, _) -> ASeq (untagAC e1, untagAA e2, ())
  | ALet (x, c, b, _) -> ALet (x, untagAC c, untagAA b, ())
  | ALetRec (xcs, b, _) -> ALetRec (List.map (fun (x, c) -> (x, untagAC c)) xcs, untagAA b, ())
  | ACExpr c -> ACExpr (untagAC c)

and untagAC (c : 'a cexpr) : unit cexpr =
  match c with
  | CPrim1 (op, e, _) -> CPrim1 (op, untagAI e, ())
  | CPrim2 (op, e1, e2, _) -> CPrim2 (op, untagAI e1, untagAI e2, ())
  | CIf (cond, thn, els, _) -> CIf (untagAI cond, untagAA thn, untagAA els, ())
  | CApp (func, args, native, _) -> CApp (untagAI func, List.map untagAI args, native, ())
  | CImmExpr i -> CImmExpr (untagAI i)
  | CTuple (es, _) -> CTuple (List.map untagAI es, ())
  | CConstruct (stru_id, fields, _) -> CConstruct (stru_id, List.map untagAI fields, ())
  | CGetter (stru, stru_offset, _) -> CGetter (untagAI stru, stru_offset, ())
  | CSetter (stru, stru_offset, new_expr, _) ->
      CSetter (untagAI stru, stru_offset, untagAI new_expr, ())
  | CIs (stru, stru_id, _) -> CIs (untagAI stru, stru_id, ())
  | CGetItem (e, idx, _) -> CGetItem (untagAI e, untagAI idx, ())
  | CSetItem (e, idx, newval, _) -> CSetItem (untagAI e, untagAI idx, untagAI newval, ())
  | CLambda (args, body, _) -> CLambda (args, untagAA body, ())

and untagAI (i : 'a immexpr) : unit immexpr =
  match i with
  | ImmNil _ -> ImmNil ()
  | ImmId (x, _) -> ImmId (x, ())
  | ImmNum (n, _) -> ImmNum (n, ())
  | ImmBool (b, _) -> ImmBool (b, ())

let atag (p : 'a aprogram) : tag aprogram =
  let next = ref 0 in
  let tag () =
    next := !next + 1;
    !next
  in
  let rec helpA (e : 'a aexpr) : tag aexpr =
    match e with
    | ASeq (e1, e2, _) ->
        let seq_tag = tag () in
        ASeq (helpC e1, helpA e2, seq_tag)
    | ALet (x, c, b, _) ->
        let let_tag = tag () in
        ALet (x, helpC c, helpA b, let_tag)
    | ALetRec (xcs, b, _) ->
        let let_tag = tag () in
        ALetRec (List.map (fun (x, c) -> (x, helpC c)) xcs, helpA b, let_tag)
    | ACExpr c -> ACExpr (helpC c)
  and helpC (c : 'a cexpr) : tag cexpr =
    match c with
    | CPrim1 (op, e, _) ->
        let prim_tag = tag () in
        CPrim1 (op, helpI e, prim_tag)
    | CPrim2 (op, e1, e2, _) ->
        let prim_tag = tag () in
        CPrim2 (op, helpI e1, helpI e2, prim_tag)
    | CIf (cond, thn, els, _) ->
        let if_tag = tag () in
        CIf (helpI cond, helpA thn, helpA els, if_tag)
    | CApp (func, args, native, _) ->
        let app_tag = tag () in
        CApp (helpI func, List.map helpI args, native, app_tag)
    | CImmExpr i -> CImmExpr (helpI i)
    | CConstruct (stru_id, fields, _) -> CConstruct (stru_id, List.map helpI fields, tag ())
    | CGetter (stru, stru_offset, _) -> CGetter (helpI stru, stru_offset, tag ())
    | CSetter (stru, stru_offset, new_expr, _) ->
        CSetter (helpI stru, stru_offset, helpI new_expr, tag ())
    | CIs (stru, stru_id, _) -> CIs (helpI stru, stru_id, tag ())
    | CTuple (es, _) ->
        let tup_tag = tag () in
        CTuple (List.map helpI es, tup_tag)
    | CGetItem (e, idx, _) ->
        let get_tag = tag () in
        CGetItem (helpI e, helpI idx, get_tag)
    | CSetItem (e, idx, newval, _) ->
        let set_tag = tag () in
        CSetItem (helpI e, helpI idx, helpI newval, set_tag)
    | CLambda (args, body, _) ->
        let lam_tag = tag () in
        CLambda (args, helpA body, lam_tag)
  and helpI (i : 'a immexpr) : tag immexpr =
    match i with
    | ImmNil _ -> ImmNil (tag ())
    | ImmId (x, _) -> ImmId (x, tag ())
    | ImmNum (n, _) -> ImmNum (n, tag ())
    | ImmBool (b, _) -> ImmBool (b, tag ())
  and helpP p =
    match p with
    | AProgram (body, _) -> AProgram (helpA body, 0)
  in
  helpP p

let expr_info (e : 'a expr) : 'a = get_tag_E e

let rec aexpr_info (e : 'a aexpr) (access : 'a -> 'b) : 'b =
  match e with
  | ASeq (_, _, x) -> access x
  | ALet (_, _, _, x) -> access x
  | ALetRec (_, _, x) -> access x
  | ACExpr x -> cexpr_info x access

and cexpr_info (e : 'a cexpr) (access : 'a -> 'b) : 'b =
  match e with
  | CPrim1 (_, _, x) -> access x
  | CPrim2 (_, _, _, x) -> access x
  | CIf (_, _, _, x) -> access x
  | CApp (_, _, _, x) -> access x
  | CTuple (_, x) -> access x
  | CGetItem (_, _, x) -> access x
  | CSetItem (_, _, _, x) -> access x
  | CLambda (_, _, x) -> access x
  | CImmExpr x -> immexpr_info x access
  | CConstruct (_, _, x) -> access x
  | CGetter (_, _, x) -> access x
  | CSetter (_, _, _, x) -> access x
  | CIs (_, _, x) -> access x

and immexpr_info (e : 'a immexpr) (access : 'a -> 'b) : 'b =
  match e with
  | ImmBool (_, x) -> access x
  | ImmNil x -> access x
  | ImmNum (_, x) -> access x
  | ImmId (_, x) -> access x

(* Helper to convert a (StringSet.t * tag) aprogram to a (string list * tag) aprogram so that *)
(* it is easier to create tests for such program *)
let rec fvs_aprog_tolist (prog : (StringSet.t * tag) aprogram) : (string list * tag) aprogram =
  let rec helpA (a : (StringSet.t * tag) aexpr) : (string list * tag) aexpr =
    match a with
    | ASeq (l, r, (fvs, tag)) -> ASeq (helpC l, helpA r, (StringSet.elements fvs, tag))
    | ALet (name, c, b, (fvs, tag)) -> ALet (name, helpC c, helpA b, (StringSet.elements fvs, tag))
    | ALetRec (binds, body, (fvs, tag)) ->
        ALetRec
          ( List.map (fun (name, b) -> (name, helpC b)) binds,
            helpA body,
            (StringSet.elements fvs, tag) )
    | ACExpr x -> ACExpr (helpC x)
  and helpC (c : (StringSet.t * tag) cexpr) : (string list * tag) cexpr =
    match c with
    | CPrim1 (op, e, (fvs, tag)) -> CPrim1 (op, helpI e, (StringSet.elements fvs, tag))
    | CPrim2 (op, l, r, (fvs, tag)) -> CPrim2 (op, helpI l, helpI r, (StringSet.elements fvs, tag))
    | CIf (cond, t, f, (fvs, tag)) ->
        CIf (helpI cond, helpA t, helpA f, (StringSet.elements fvs, tag))
    | CApp (func, args, call_type, (fvs, tag)) ->
        CApp (helpI func, List.map helpI args, call_type, (StringSet.elements fvs, tag))
    | CTuple (elems, (fvs, tag)) -> CTuple (List.map helpI elems, (StringSet.elements fvs, tag))
    | CGetItem (tup, idx, (fvs, tag)) ->
        CGetItem (helpI tup, helpI idx, (StringSet.elements fvs, tag))
    | CSetItem (tup, idx, e, (fvs, tag)) ->
        CSetItem (helpI tup, helpI idx, helpI e, (StringSet.elements fvs, tag))
    | CLambda (args, body, (fvs, tag)) -> CLambda (args, helpA body, (StringSet.elements fvs, tag))
    | CConstruct (stru_id, fields, (fvs, tag)) ->
        CConstruct (stru_id, List.map helpI fields, (StringSet.elements fvs, tag))
    | CGetter (stru, stru_offset, (fvs, tag)) ->
        CGetter (helpI stru, stru_offset, (StringSet.elements fvs, tag))
    | CSetter (stru, stru_offset, new_expr, (fvs, tag)) ->
        CSetter (helpI stru, stru_offset, helpI new_expr, (StringSet.elements fvs, tag))
    | CIs (stru, stru_id, (fvs, tag)) -> CIs (helpI stru, stru_id, (StringSet.elements fvs, tag))
    | CImmExpr x -> CImmExpr (helpI x)
  and helpI (i : (StringSet.t * tag) immexpr) : (string list * tag) immexpr =
    match i with
    | ImmBool (v, (fvs, tag)) -> ImmBool (v, (StringSet.elements fvs, tag))
    | ImmNil (fvs, tag) -> ImmNil (StringSet.elements fvs, tag)
    | ImmNum (v, (fvs, tag)) -> ImmNum (v, (StringSet.elements fvs, tag))
    | ImmId (v, (fvs, tag)) -> ImmId (v, (StringSet.elements fvs, tag))
  in
  match prog with
  | AProgram (body, (fvs, tag)) -> AProgram (helpA body, (StringSet.elements fvs, tag))
