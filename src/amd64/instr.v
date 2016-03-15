(*===========================================================================
    Instruction type and helpers

    Notation to support Intel-style syntax is defined in instrsyntax.v.

    Instructions are *not* in one-to-one correspondence with binary formats,
    as there may be more than one way of encoding the same instruction e.g.
    - short and long forms for constants (e.g. PUSH constant)
    - special casing (e.g. special forms for EAX/AL register, special form for RET 0)
    - symmetry in direction (e.g. MOV r1, r2 has two encodings)
  ===========================================================================*)
(* We need ssreflect for the [if ... then ... else ...] syntax in an inlineable way. *)
From mathcomp Require Import ssreflect.
Require Import bitsrep reg.

Inductive scale := S1 | S2 | S4 | S8.

Inductive memspec :=
  mkMemSpec (sib : option reg * option (gpReg * scale))
            (offset : option DWORD).

(* Register or memory *)
Inductive regmem s :=
| RegMemR (r: gpVReg s) :> regmem s
| RegMemM (ms: memspec).
Inductive regimm s :=
| RegImmI (c: VWORD s)
| RegImmR (r: gpVReg s) :> regimm s.

Coercion DWORDRegMemM (ms: memspec) := RegMemM OpSize4 ms.
Coercion DWORDRegImmI (d: DWORD)    := RegImmI OpSize4 d.

(* Unary ops: immediate, register, or memory source *)
(* Binary ops: five combinations of source and destination *)
Inductive src :=
| SrcI (c: DWORD) :> src
| SrcM (ms: memspec) :> src
| SrcR (r: gpReg) :> src.

Inductive dstsrc (s: opsize) :=
| DstSrcRR (dst src: gpVReg s)
| DstSrcRM (dst: gpVReg s) (src: memspec)
| DstSrcMR (dst: memspec) (src: gpVReg s)
| DstSrcRI (dst: gpVReg s) (c: VWORD s)
| DstSrcMI (dst: memspec) (c: VWORD s).

(* We could support 32-bit operands there (for MOVD) *)
Inductive xmmdstsrc :=
| XMMDstSrcXRM (dst : XMMreg) (src : regmem OpSize8)
| XMMDstSrcRMX (dst : regmem OpSize8) (src : XMMreg).

(* Jump target: PC-relative offset *)
(* We make this a separate type constructor to pick up type class instances later *)
(* Jump ops: immediate, register, or memory source *)
Inductive Tgt :=
| mkTgt :> DWORD -> Tgt.
Inductive JmpTgt :=
| JmpTgtI :> Tgt -> JmpTgt
| JmpTgtM :> memspec -> JmpTgt
| JmpTgtR :> reg -> JmpTgt.
Inductive ShiftCount :=
| ShiftCountCL | ShiftCountI (c: BYTE).
Inductive Port :=
| PortI :> BYTE -> Port
| PortDX : Port.

(* All binary operations come in byte and dword flavours, specified in the instruction *)
(* Unary operations come in byte and dword flavours, except for POP *)
Inductive BinOp :=
| OP_ADC | OP_ADD | OP_AND | OP_CMP | OP_OR | OP_SBB | OP_SUB | OP_XOR.
Inductive UnaryOp :=
| OP_INC | OP_DEC | OP_NOT | OP_NEG.
Inductive BitOp :=
| OP_BT | OP_BTC | OP_BTR | OP_BTS.
Inductive ShiftOp :=
| OP_ROL | OP_ROR | OP_RCL | OP_RCR | OP_SHL | OP_SHR | OP_SAL | OP_SAR.

Inductive Condition :=
| CC_O | CC_B | CC_Z | CC_BE | CC_S | CC_P | CC_L | CC_LE.

Inductive Instr :=
| UOP s (op: UnaryOp) (dst: regmem s)
| BOP s (op: BinOp) (ds: dstsrc s)
| BITOP (op: BitOp) (dst: regmem OpSize4) (bit: gpReg + BYTE)
| TESTOP s (dst: regmem s) (src: regimm s)
| MOVOP s (ds: dstsrc s)
| MOVABS (dst : gpReg) (src : QWORD)
| MOVX (signextend:bool) s (dst: gpReg) (src: regmem s)
| MOVQ (ds : xmmdstsrc)
| SHIFTOP s (op: ShiftOp) (dst: regmem s) (count: ShiftCount)
| MUL {s} (src: regmem s)
| IMUL s (dst: gpVReg s) (src: regmem s)
| IMULimm s (dst: gpVReg s) (src: regmem s) (i : VWORD s)
| IDIV {s} (src : regmem s)
| LEA (reg: gpReg) (src: regmem OpSize4)
| XCHG s (reg: gpVReg s) (src: regmem s)
| JCCrel (cc: Condition) (cv: bool) (tgt: Tgt)
| SET (cc : Condition) (cv : bool) (r : gpVReg OpSize1)

(* Only 64-bit values can be pushed, although we could have allowed 16-bit
values too. Push for 32-bit values cannot be encoded in x86-64. *)
| PUSH (src: src)
| POP (dst: regmem OpSize4)
| CALLrel (tgt: JmpTgt) | JMPrel (tgt: JmpTgt)
| RETOP (size: WORD)
| CQO
| HLT | ENCLU | ENCLS | BADINSTR.