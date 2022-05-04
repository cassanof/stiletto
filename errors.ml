open Printf
open Exprs
open Pretty

exception ParseError of string (* parse-error message *)
exception UnboundId of string * sourcespan (* name, where used *)
exception UnboundFun of string * sourcespan (* name of fun, where used *)
exception ShadowId of string * sourcespan * sourcespan (* name, where used, where defined *)
exception DuplicateId of string * sourcespan * sourcespan (* name, where used, where defined *)
exception DuplicateFun of string * sourcespan * sourcespan (* name, where used, where defined *)
exception Overflow of int64 * sourcespan (* value, where used *)
exception Arity of int * int * sourcespan (* intended arity, actual arity, where called *)
exception NotYetImplemented of string
exception Unsupported of string * sourcespan
exception InternalCompilerError of string (* Major failure: message to show *)
exception LetRecNonFunction of sourcespan bind * sourcespan (* name binding, where defined *)
exception ShouldBeFunction of string * sourcespan (* name, where defined, actual typ *)
exception DeclArity of string * int * int * sourcespan (* name, num args, num types, where defined *)
exception UnboundStruct of string * sourcespan (* name, where used *)
exception StructArity of int * int * sourcespan (* intended arity, actual arity, where constructed *)
exception DuplicateStruct of string * sourcespan * sourcespan (* name, where used, where defined *)
exception DuplicateField of string * sourcespan (* name, struct position *)
exception DuplicateMethod of string * sourcespan * sourcespan (* name, where used, where defined *)


  

(* Stringifies a list of compilation errors *)
let print_errors (exns : exn list) : string list =
  List.map (fun e ->
      match e with
      | ParseError msg -> msg
      | NotYetImplemented msg ->
         "Not yet implemented: " ^ msg
      | Unsupported(msg, loc) ->
         sprintf "Unsupported: %s at <%s>" msg (string_of_sourcespan loc)
      | InternalCompilerError msg ->
         "Internal Compiler Error: " ^ msg
      | UnboundId(x, loc) ->
         sprintf "The identifier %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
      | UnboundFun(x, loc) ->
         sprintf "The function name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
      | ShadowId(x, loc, existing) ->
         sprintf "The identifier %s, defined at <%s>, shadows one defined at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | DuplicateId(x, loc, existing) ->
         sprintf "The identifier %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | DuplicateFun(x, loc, existing) ->
         sprintf "The function name %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | Overflow(num, loc) ->
         sprintf "The number literal %Ld, used at <%s>, is not supported in this language"
                 num (string_of_sourcespan loc)
      | Arity(expected, actual, loc) ->
         sprintf "The function called at <%s> expected an arity of %d, but received %d arguments"
                 (string_of_sourcespan loc) expected actual
      | DeclArity(name, num_args, num_types, loc) ->
         sprintf "The function %s, defined at %s, has %d arguments but only %d types provided"
                 name (string_of_sourcespan loc) num_args num_types
      | ShouldBeFunction(name, loc) ->
         sprintf "The function %s, at %s, should be function" name (string_of_sourcespan loc)
      | LetRecNonFunction(bind, loc) ->
         sprintf "Binding error at %s: Let-rec expected a name binding to a lambda; got %s"
           (string_of_sourcespan loc) (string_of_bind bind)
      | UnboundStruct(x, loc) ->
         sprintf "The struct name %s, used at <%s>, is not in scope" x (string_of_sourcespan loc)
      | StructArity(expected, actual, loc) ->
         sprintf "The constructor called at <%s> expected an arity of %d, but received %d arguments"
                 (string_of_sourcespan loc) expected actual
      | DuplicateStruct(x, loc, existing) ->
         sprintf "The struct %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | DuplicateField (x, loc) ->
          sprintf "The field %s, redefined in the struct at <%s>, duplicates one other field in the same struct" x
            (string_of_sourcespan loc)
      | DuplicateMethod(x, loc, existing) ->
         sprintf "The method %s, redefined at <%s>, duplicates one at <%s>"
                 x (string_of_sourcespan loc) (string_of_sourcespan existing)
      | _ ->
         sprintf "%s" (Printexc.to_string e)
    ) exns
;;

