open Printf

(* Abstract syntax of (a small subset of) x86 assembly instructions *)
let word_size = 8

type reg =
  | RAX
  | RSP
  | RBP
  | RSI
  | RDI
  | RDX
  | RCX
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | RBX
  | CL
  | AL

type size =
  | QWORD_PTR
  | DWORD_PTR
  | WORD_PTR
  | BYTE_PTR

type arg =
  | Const of int64
  | HexConst of int64
  | Reg of reg
  | RegOffset of int * reg (* int is # words of offset *)
  | RegOffsetReg of reg * reg * int * int
  | Sized of size * arg
  | LabelContents of string
  | Label of string

type instruction =
  | IMov of arg * arg
  | IAdd of arg * arg
  | ISub of arg * arg
  | IMul of arg * arg
  | IShl of arg * arg
  | IShr of arg * arg
  | ISar of arg * arg
  | IAnd of arg * arg
  | IOr of arg * arg
  | IXor of arg * arg
  | ILabel of string
  | IPush of arg
  | IPop of arg
  | ICall of arg
  | IRet
  | ICmp of arg * arg
  | ITest of arg * arg
  | ISete of arg
  | IJo of arg
  | IJno of arg
  | IJe of arg
  | IJne of arg
  | IJl of arg
  | IJle of arg
  | IJg of arg
  | IJge of arg
  | IJmp of arg
  | IJz of arg
  | IJnz of arg
  | ILineComment of string
  | IInstrComment of instruction * string

let r_to_asm (r : reg) : string =
  match r with
  | RAX -> "RAX"
  | RSI -> "RSI"
  | RDI -> "RDI"
  | RCX -> "RCX"
  | RDX -> "RDX"
  | RSP -> "RSP"
  | RBP -> "RBP"
  | R8 -> "R8"
  | R9 -> "R9"
  | R10 -> "R10"
  | R11 -> "R11"
  | R12 -> "R12"
  | R13 -> "R13"
  | R14 -> "R14"
  | R15 -> "R15"
  | RBX -> "RBX"
  | CL -> "CL"
  | AL -> "AL"

let rec arg_to_asm (a : arg) : string =
  match a with
  | Const n -> sprintf "%Ld" n
  | HexConst n -> sprintf "0x%Lx" n
  | Reg r -> r_to_asm r
  | RegOffset (n, r) ->
      if n >= 0 then sprintf "[%s+%d]" (r_to_asm r) n else sprintf "[%s-%d]" (r_to_asm r) (-1 * n)
  | RegOffsetReg (r1, r2, mul, off) ->
      sprintf "[%s + %s * %d + %d]" (r_to_asm r1) (r_to_asm r2) mul off
  | Sized (size, a) ->
      sprintf "%s %s"
        ( match size with
        | QWORD_PTR -> "QWORD"
        | DWORD_PTR -> "DWORD"
        | WORD_PTR -> "WORD"
        | BYTE_PTR -> "BYTE" )
        (arg_to_asm a)
  | LabelContents s -> sprintf "[%s]" s
  | Label s -> s

let rec i_to_asm (i : instruction) : string =
  match i with
  | IMov (dest, value) -> sprintf "  mov %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IAdd (dest, to_add) -> sprintf "  add %s, %s" (arg_to_asm dest) (arg_to_asm to_add)
  | ISub (dest, to_sub) -> sprintf "  sub %s, %s" (arg_to_asm dest) (arg_to_asm to_sub)
  | IMul (dest, to_mul) -> sprintf "  imul %s, %s" (arg_to_asm dest) (arg_to_asm to_mul)
  | ICmp (left, right) -> sprintf "  cmp %s, %s" (arg_to_asm left) (arg_to_asm right)
  | ILabel name -> "align 16\n" ^ name ^ ":"
  | IJo label -> sprintf "  jo near %s" (arg_to_asm label)
  | IJno label -> sprintf "  jno near %s" (arg_to_asm label)
  | IJe label -> sprintf "  je near %s" (arg_to_asm label)
  | IJne label -> sprintf "  jne near %s" (arg_to_asm label)
  | IJl label -> sprintf "  jl near %s" (arg_to_asm label)
  | IJle label -> sprintf "  jle near %s" (arg_to_asm label)
  | IJg label -> sprintf "  jg near %s" (arg_to_asm label)
  | IJge label -> sprintf "  jge near %s" (arg_to_asm label)
  | IJmp label -> sprintf "  jmp near %s" (arg_to_asm label)
  | IJz label -> sprintf "  jz near %s" (arg_to_asm label)
  | IJnz label -> sprintf "  jnz near %s" (arg_to_asm label)
  | IAnd (dest, value) -> sprintf "  and %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IOr (dest, value) -> sprintf "  or %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IXor (dest, value) -> sprintf "  xor %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShl (dest, value) -> sprintf "  shl %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IShr (dest, value) -> sprintf "  shr %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | ISar (dest, value) -> sprintf "  sar %s, %s" (arg_to_asm dest) (arg_to_asm value)
  | IPush value -> sprintf "  push %s" (arg_to_asm value)
  | IPop dest -> sprintf "  pop %s" (arg_to_asm dest)
  | ICall label -> sprintf "  call %s" (arg_to_asm label)
  | IRet -> "  ret"
  | ITest (arg, comp) -> sprintf "  test %s, %s" (arg_to_asm arg) (arg_to_asm comp)
  | ISete arg -> sprintf "  sete %s" (arg_to_asm arg)
  | ILineComment str -> sprintf "  ;; %s" str
  | IInstrComment (instr, str) -> sprintf "%s ; %s" (i_to_asm instr) str

let to_asm (is : instruction list) : string =
  List.fold_left (fun s i -> sprintf "%s\n%s" s (i_to_asm i)) "" is
