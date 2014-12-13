open Printf

open Bitsrep
open Reg
open Instr
open Program

let print_option print oc = function
| None -> ()
| Some x -> print oc x

let print_uop oc = function
| OP_INC -> fprintf oc "inc"
| OP_DEC -> fprintf oc "dec"
| OP_NOT -> fprintf oc "not"
| OP_NEG -> fprintf oc "neg"

let print_bop oc = function
| OP_ADC -> fprintf oc "adc"
| OP_ADD -> fprintf oc "add"
| OP_AND -> fprintf oc "and"
| OP_CMP -> fprintf oc "cmp"
| OP_OR  -> fprintf oc "or"
| OP_SBB -> fprintf oc "sbb"
| OP_SUB -> fprintf oc "sub"
| OP_XOR -> fprintf oc "xor"


let print_opsize oc = function
| OpSize1 -> fprintf oc "b"
| OpSize2 -> fprintf oc "w"
| OpSize4 -> fprintf oc "l"
| OpSize8 -> fprintf oc "q"

let print_gpreg_byte oc = function
| RAX -> fprintf oc "%%al"
| RBX -> fprintf oc "%%bl"
| RCX -> fprintf oc "%%cl"
| RDX -> fprintf oc "%%dl"
| RSI -> fprintf oc "%%sil"
| RDI -> fprintf oc "%%dil"
| RBP -> fprintf oc "%%bpl"
| RSP -> fprintf oc "%%spl"
| R8 -> fprintf oc "%%r8b"
| R9 -> fprintf oc "%%r9b"
| R10 -> fprintf oc "%%r10b"
| R11 -> fprintf oc "%%r11b"
| R12 -> fprintf oc "%%r12b"
| R13 -> fprintf oc "%%r13b"
| R14 -> fprintf oc "%%r14b"
| R15 -> fprintf oc "%%r15b"

let print_gpreg_word oc = function
| RAX -> fprintf oc "%%ax"
| RBX -> fprintf oc "%%bx"
| RCX -> fprintf oc "%%cx"
| RDX -> fprintf oc "%%dx"
| RSI -> fprintf oc "%%si"
| RDI -> fprintf oc "%%di"
| RBP -> fprintf oc "%%bp"
| RSP -> fprintf oc "%%sp"
| R8 -> fprintf oc "%%r8w"
| R9 -> fprintf oc "%%r9w"
| R10 -> fprintf oc "%%r10w"
| R11 -> fprintf oc "%%r11w"
| R12 -> fprintf oc "%%r12w"
| R13 -> fprintf oc "%%r13w"
| R14 -> fprintf oc "%%r14w"
| R15 -> fprintf oc "%%r15w"

let print_gpreg_dword oc = function
| RAX -> fprintf oc "%%eax"
| RBX -> fprintf oc "%%ebx"
| RCX -> fprintf oc "%%ecx"
| RDX -> fprintf oc "%%edx"
| RSI -> fprintf oc "%%esi"
| RDI -> fprintf oc "%%edi"
| RBP -> fprintf oc "%%ebp"
| RSP -> fprintf oc "%%esp"
| R8 -> fprintf oc "%%r8d"
| R9 -> fprintf oc "%%r9d"
| R10 -> fprintf oc "%%r10d"
| R11 -> fprintf oc "%%r11d"
| R12 -> fprintf oc "%%r12d"
| R13 -> fprintf oc "%%r13d"
| R14 -> fprintf oc "%%r14d"
| R15 -> fprintf oc "%%r15d"

let print_gpreg oc = function
| RAX -> fprintf oc "%%rax"
| RBX -> fprintf oc "%%rbx"
| RCX -> fprintf oc "%%rcx"
| RDX -> fprintf oc "%%rdx"
| RSI -> fprintf oc "%%rsi"
| RDI -> fprintf oc "%%rdi"
| RBP -> fprintf oc "%%rbp"
| RSP -> fprintf oc "%%rsp"
| R8 -> fprintf oc "%%r8"
| R9 -> fprintf oc "%%r9"
| R10 -> fprintf oc "%%r10"
| R11 -> fprintf oc "%%r11"
| R12 -> fprintf oc "%%r12"
| R13 -> fprintf oc "%%r13"
| R14 -> fprintf oc "%%r14"
| R15 -> fprintf oc "%%r15"

let print_gpVReg = function
| OpSize1 -> fun oc x -> print_gpreg_byte oc (Obj.magic x)
| OpSize2 -> fun oc x -> print_gpreg_word oc (Obj.magic x)
| OpSize4 -> fun oc x -> print_gpreg_dword oc (Obj.magic x)
| OpSize8 -> fun oc x -> print_gpreg oc (Obj.magic x)

let print_reg oc = function
| GPReg r -> print_gpreg oc r
| RIP -> fprintf oc "%%rip"

let print_scale oc = function
| S1 -> fprintf oc "1"
| S2 -> fprintf oc "2"
| S4 -> fprintf oc "4"
| S8 -> fprintf oc "8"

let print_byte oc w = fprintf oc "%i" (toZ 7 w)
let print_word oc w = fprintf oc "%i" (toZ 15 w)
let print_dword oc w = fprintf oc "%i" (toZ 31 w)
let print_qword oc w = fprintf oc "%i" (toZ 63 w)

let print_vword = function
| OpSize1 -> print_byte
| OpSize2 -> print_word
| OpSize4 -> print_dword
| OpSize8 -> print_dword

let print_data oc d =
  match List.length d with
  | 8 -> fprintf oc ".byte %a" print_byte d
  | 16 -> fprintf oc ".word %a" print_word d
  | 32 -> fprintf oc ".dword %a" print_dword d
  | 64 -> fprintf oc ".quad %a" print_qword d
  | _ -> assert false

let print_memspec oc = function
| Coq_mkMemSpec ((Some base,None),off) ->
    fprintf oc "%a(%a)" (print_option print_dword) off print_reg base
| Coq_mkMemSpec ((obase,Some (index,scale)),off) ->
   fprintf oc "%a(%a,%a,%a)" (print_option print_dword) off
     (print_option print_reg) obase print_gpreg index print_scale scale
| _ -> assert false

let print_xmmreg oc = function
| YMM0 -> fprintf oc "XMM0"
| YMM1 -> fprintf oc "XMM1"
| YMM2 -> fprintf oc "XMM2"
| YMM3 -> fprintf oc "XMM3"
| YMM4 -> fprintf oc "XMM4"
| YMM5 -> fprintf oc "XMM5"
| YMM6 -> fprintf oc "XMM6"
| YMM7 -> fprintf oc "XMM7"
| YMM8 -> fprintf oc "XMM8"
| YMM9 -> fprintf oc "XMM9"
| YMM10 -> fprintf oc "XMM10"
| YMM11 -> fprintf oc "XMM11"
| YMM12 -> fprintf oc "XMM12"
| YMM13 -> fprintf oc "XMM13"
| YMM14 -> fprintf oc "XMM14"
| YMM15 -> fprintf oc "XMM15"

let print_dstsrc size oc = function
| DstSrcRR (dst,src) -> fprintf oc "%a, %a" (print_gpVReg size) src (print_gpVReg size) dst
| DstSrcRM (dst,src) -> fprintf oc "%a, %a" print_memspec src (print_gpVReg size) dst
| DstSrcMR (dst,src) -> fprintf oc "%a, %a" (print_gpVReg size) src print_memspec dst
| DstSrcRI (dst,src) -> fprintf oc "%a, %a" (print_vword size) src (print_gpVReg size) dst
| DstSrcMI (dst,src) -> fprintf oc "%a, %a" (print_vword size) src print_memspec dst

let print_regmem size oc = function
| RegMemR r -> print_gpVReg size oc r
| RegMemM ms -> print_memspec oc ms

let print_regimm size oc = function
| RegImmI w -> print_vword size oc w
| RegImmR r -> print_gpVReg size oc r

let print_xmmdstsrc oc = function
| XMMDstSrcXRM (r,rm) -> fprintf oc "%a, %a" (print_regmem OpSize8) rm print_xmmreg r
| XMMDstSrcRMX (rm,r) -> fprintf oc "%a, %a" print_xmmreg r (print_regmem OpSize8) rm

let print_jump_condition oc = function
| CC_O -> fprintf oc "o"
| CC_B -> fprintf oc "b"
| CC_Z -> fprintf oc "z"
| CC_BE -> fprintf oc "be"
| CC_S -> fprintf oc "s"
| CC_P -> fprintf oc "p"
| CC_L -> fprintf oc "l"
| CC_LE -> fprintf oc "le"

let print_negation oc b =
  if b then () else fprintf oc "n"

let print_jump_tgt oc = function
| JmpTgtI w -> print_dword oc w
| JmpTgtM ms -> print_memspec oc ms
| JmpTgtR r -> print_reg oc r

let print_instr oc = function
| UOP (size,op,regmem) ->
    fprintf oc "%a%a %a" print_uop op print_opsize size (print_regmem size) regmem
| BOP (size,op,dstsrc) ->
    fprintf oc "%a%a %a" print_bop op print_opsize size (print_dstsrc size) dstsrc
| BITOP _ -> assert false (* coq_BitOp * regmem * (gpReg, coq_BYTE) sum *)
| TESTOP (size,dst,src) ->
    fprintf oc "test%a %a, %a" print_opsize size (print_regimm size) src (print_regmem size) dst
| MOVOP (size,dstsrc) ->
    fprintf oc "mov%a %a" print_opsize size (print_dstsrc size) dstsrc
| MOVABS (dst,w) -> fprintf oc "movabsq %a, %a" print_qword w print_gpreg dst
| MOVX (b,size,dst,src) ->
   if b then assert false else
     fprintf oc "movzb%a %a, %a" print_opsize size (print_regmem size) src print_gpreg dst
| MOVQ dstsrc -> fprintf oc "movabsq %a" print_xmmdstsrc dstsrc
| SHIFTOP (size,op,dst,count) -> assert false (* opsize * coq_ShiftOp * regmem * coq_ShiftCount *)
| MUL (size, dst) -> fprintf oc "mul%a %a" print_opsize size (print_regmem size) dst
| IMUL (size, dst, src) -> fprintf oc "imul%a %a, %a" print_opsize size (print_regmem size) src (print_gpVReg size) dst
| IMULimm (size, dst, src1, src2) ->
   fprintf oc "imul%a %a, %a, %a" print_opsize size (print_vword size) src2 (print_regmem size) src1 (print_gpVReg size) dst
| IDIV (size,dst) -> fprintf oc "idiv%a %a" print_opsize size (print_regmem size) dst
| LEA (dst,src) -> fprintf oc "leaq %a, %a" (print_regmem OpSize8) src print_gpreg dst
| XCHG (size,dst,src) ->
    fprintf oc "xchg%a %a, %a" print_opsize size (print_regmem size) src
     (print_gpVReg size) dst
| JCCrel (c,b,tgt) -> fprintf oc "j%a%a %a" print_jump_condition c print_negation b print_dword tgt
| SET (c,b,dst) -> fprintf oc "set%a%a %a" print_jump_condition c print_negation b print_gpreg_byte dst
| PUSH src -> assert false
| POP dst -> assert false (* regmem *)
| CALLrel tgt -> fprintf oc "call %a" print_jump_tgt tgt
| JMPrel tgt -> fprintf oc "jmp %a" print_jump_tgt tgt
| RETOP w -> fprintf oc "ret %a" print_word w (* TODO: specialize *)
| CQO -> fprintf oc "cqto"
| HLT
| ENCLU
| ENCLS
| BADINSTR -> fprintf oc "badinstr"


let rec print_program oc = function
| Coq_prog_instr i -> print_instr oc i
| Coq_prog_skip -> ()
| Coq_prog_seq (p1,p2) -> fprintf oc "%a\n%a" print_program p1 print_program p2
| Coq_prog_declabel f -> print_program oc (f (fromNat 32 0))
| Coq_prog_label w -> fprintf oc "%a:" print_dword w
| Coq_prog_data (_,_,data) -> print_data oc (Obj.magic data)

let _ = OcamlbindState.register_fun "print_program" (Obj.magic (print_program
stdout))
