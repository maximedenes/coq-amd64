(*===========================================================================
    Notation to simulate Intel x86 instruction syntax
    You can cut-and-paste this notation into inline assembler in VS!
  ===========================================================================*)
Require Import ZArith.
From Ssreflect Require Import ssreflect ssrbool seq.
Require Import bitsrep bitsops amd64.reg amd64.instr.
Require Export Coq.Strings.String.

Delimit Scope instr_scope with asm.
Delimit Scope memspec_scope with ms.

Local Open Scope Z_scope.

(*---------------------------------------------------------------------------
    MemSpec notation
  ---------------------------------------------------------------------------*)
Inductive SingletonMemSpec :=
| OffsetMemSpec :> DWORD -> SingletonMemSpec
| RegMemSpec :> baseReg -> SingletonMemSpec.

Definition fromSingletonMemSpec (msa: SingletonMemSpec) :=
  match msa with
  | OffsetMemSpec d => mkMemSpec (None,None) (Some d)
  | RegMemSpec r => mkMemSpec (Some r,None) None
  end.

Definition VWORDasIMM s : VWORD s -> option (IMM s) :=
  match s with
  | OpSize1 => fun x => Some x
  | OpSize2 => fun x => Some x
  | OpSize4 => fun x => Some x
  | OpSize8 => fun x => None
  end.
Hint Unfold VWORDasIMM : instrsyntax.


Notation "'[' m ']'" :=
  (fromSingletonMemSpec m)
  (at level 0, m at level 0) : memspec_scope.

Notation "'[' r '+' n ']'" :=
  (mkMemSpec (Some r, None) (Some n))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' n ']'" :=
  (mkMemSpec (Some (r:baseReg), None) (Some (n:DWORD)))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '-' n ']'" :=
  (mkMemSpec (Some r, None) (Some (negB n)))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '-' n ']'" :=
  (mkMemSpec (Some (r:baseReg), None) (Some (negB n)))
  (at level 0, r at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '+' n ']'" :=
  (mkMemSpec (Some r, Some (i,S1)) (Some n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '+' n ']'" :=
  (mkMemSpec (Some (r:baseReg), Some (i: ixReg,S1)) (Some (n:DWORD)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '-' n ']'" :=
  (mkMemSpec (Some r, Some (i, S1)) (Some (negB n)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '-' n ']'" :=
  (mkMemSpec (Some (r:baseReg), Some (i: ixReg,S1)) (Some (negB n)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '2' ']'" :=
  (mkMemSpec (Some (r:baseReg), Some(i: ixReg,S2)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' ']'" :=
  (mkMemSpec (Some (r:baseReg), Some(i: ixReg,S2)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" :=
  (mkMemSpec (Some r, Some(i,S2)) (Some n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '2' '+' n ']'" :=
  (mkMemSpec (Some (r: baseReg), Some(i: ixReg,S2)) (Some (n:DWORD)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '4' ']'" :=
  (mkMemSpec (Some r, Some(i,S4)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' ']'" :=
  (mkMemSpec (Some (r: baseReg), Some(i: ixReg,S4)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" :=
  (mkMemSpec (Some r, Some(i,S4)) (Some (n:DWORD)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '4' '+' n ']'" :=
  (mkMemSpec (Some (r: baseReg), Some(i: ixReg,S4)) (Some (n:DWORD)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '8' ']'" :=
  (mkMemSpec (Some r, Some(i,S8)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' ']'" :=
  (mkMemSpec (Some (r: baseReg), Some(i: ixReg,S8)) None)
  (at level 0, r at level 0, i at level 0) : instr_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" :=
  (mkMemSpec (Some r, Some(i,S8)) (Some n))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' r '+' i '*' '8' '+' n ']'" :=
  (mkMemSpec (Some (r:baseReg), Some(i: ixReg,S8)) (Some (n:DWORD)))
  (at level 0, r at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '2' ']'" :=
  (mkMemSpec (None, Some(i,S2)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '2' ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S2)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '2' '+' n ']'" :=
  (mkMemSpec (None, Some(i,S2)) (Some n))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '2' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S2)) (Some n))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '2' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S2)) (Some (n:DWORD)))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '4' ']'" :=
  (mkMemSpec (None, Some(i,S4)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '4' ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S4)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '4' '+' n ']'" :=
  (mkMemSpec (None, Some(i,S4)) (Some n))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '4' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S4)) (Some n))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '4' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S4)) (Some (n:DWORD)))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '8' ']'" :=
  (mkMemSpec (None, Some(i,S8)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '8' ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S8)) None)
  (at level 0, i at level 0) : instr_scope.

Notation "'[' i '*' '8' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S8)) (Some n))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' i '*' '8' '+' n ']'" :=
  (mkMemSpec (None, Some(i:ixReg,S8)) (Some (n:DWORD)))
  (at level 0, i at level 0, n at level 0) : memspec_scope.

Notation "'[' 'RIP' '+' n ']'" :=
  (RIPrel (n: DWORD)).


Example exMemSpec1 := [RBX]%ms.
(* Non-example: we cannot address memory through a 32-bit (or less) register: 
Example exMemSpec2 := [EBP]%ms.
*)
Example exMemSpec3 := [R10+R12*4+12]%ms.
Example exMemSpec6 := [RIP+213]%ms.
Open Scope instr_scope.

Bind Scope memspec_scope with memspec.

Inductive InstrArg :=
| InstrArgR s :> gpVReg s -> InstrArg
| InstrArgM :> memspec -> InstrArg
| InstrArgXMM :> XMMreg -> InstrArg.

Inductive InstrSrc :=
| ArgSrc :> InstrArg -> InstrSrc
| ConstSrc :> DWORD -> InstrSrc
| QConstSrc :> QWORD -> InstrSrc.

Bind Scope memspec_scope with memspec.

(*---------------------------------------------------------------------------
    Unary operations
  ---------------------------------------------------------------------------*)
Notation "'NOT' x"
  := (UOP _ OP_NOT x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NOT' 'BYTE' m"
  := (UOP OpSize1 OP_NOT (RegMemM OpSize1 m%ms)) (m at level 55, at level 60) : instr_scope.

Example exNOT3 := NOT EAX. 
Example exNOT2 := NOT [RBX+RCX*4+9].

Notation "'NEG' x"
  := (UOP _ OP_NEG x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'NEG' 'BYTE' m"
  := (UOP OpSize1 OP_NEG (RegMemM OpSize1 m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'INC' x"
  := (UOP _ OP_INC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'INC' 'BYTE' m"
  := (UOP OpSize1 OP_INC (RegMemM OpSize1 m%ms)) (m at level 55, at level 60) : instr_scope.
Notation "'DEC' x"
  := (UOP _ OP_DEC x%ms) (x at level 55, at level 60) : instr_scope.
Notation "'DEC' 'BYTE' m"
  := (UOP OpSize1 OP_DEC (RegMemM OpSize1 m%ms)) (m at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    Binary operations
  ---------------------------------------------------------------------------*)
Definition makeBOP op dst (src: InstrSrc) :=
  match dst, src with
  | InstrArgR OpSize1 dst, InstrArgR OpSize1 src => BOP OpSize1 op (DstSrcRR OpSize1 dst src)
  | InstrArgR OpSize2 dst, InstrArgR OpSize2 src => BOP OpSize2 op (DstSrcRR OpSize2 dst src)
  | InstrArgR OpSize4 dst, InstrArgR OpSize4 src => BOP OpSize4 op (DstSrcRR OpSize4 dst src)
  | InstrArgR OpSize8 dst, InstrArgR OpSize8 src => BOP OpSize8 op (DstSrcRR OpSize8 dst src)

  | InstrArgR OpSize1 dst, InstrArgM src => BOP OpSize1 op (DstSrcRM OpSize1 dst src)
  | InstrArgR OpSize2 dst, InstrArgM src => BOP OpSize2 op (DstSrcRM OpSize2 dst src)
  | InstrArgR OpSize4 dst, InstrArgM src => BOP OpSize4 op (DstSrcRM OpSize4 dst src)
  | InstrArgR OpSize8 dst, InstrArgM src => BOP OpSize8 op (DstSrcRM OpSize8 dst src)

  | InstrArgR OpSize1 dst, ConstSrc n => BOP OpSize1 op (DstSrcRI OpSize1 dst (low 8 n))
  | InstrArgR OpSize4 dst, ConstSrc n => BOP OpSize4 op (DstSrcRI OpSize4 dst n)
  | InstrArgR OpSize8 dst, ConstSrc n => BOP OpSize8 op (DstSrcRI OpSize8 dst n)

  | InstrArgM dst, InstrArgR OpSize1 src => BOP OpSize1 op (DstSrcMR OpSize1 dst src)
  | InstrArgM dst, InstrArgR OpSize2 src => BOP OpSize2 op (DstSrcMR OpSize2 dst src)
  | InstrArgM dst, InstrArgR OpSize4 src => BOP OpSize4 op (DstSrcMR OpSize4 dst src)
  | InstrArgM dst, InstrArgR OpSize8 src => BOP OpSize8 op (DstSrcMR OpSize8 dst src)

  | InstrArgM dst, ConstSrc n => BOP OpSize4 op (DstSrcMI OpSize4 dst n)
  | _, _=> BADINSTR
  end.

Notation "'ADC' x , y" := (makeBOP OP_ADC x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' x , y" := (makeBOP OP_ADD x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' x , y" := (makeBOP OP_SUB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' x , y" := (makeBOP OP_SBB x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' x , y" := (makeBOP OP_AND x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' x , y" := (makeBOP OP_OR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' x , y" := (makeBOP OP_XOR x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' x , y" := (makeBOP OP_CMP x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

(* Only need byte modifier for constant source, memspec destination *)
Notation "'ADC' 'BYTE' x , y" :=
  (BOP OpSize1 OP_ADC (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'ADD' 'BYTE' x , y" :=
  (BOP OpSize1 OP_ADD (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SUB' 'BYTE' x , y" :=
  (BOP OpSize1 OP_SUB (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'SBB' 'BYTE' x , y" :=
  (BOP OpSize1 OP_SBB (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'AND' 'BYTE' x , y" :=
  (BOP OpSize1 OP_AND (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'OR' 'BYTE' x , y" :=
  (BOP OpSize1 OP_OR (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'XOR' 'BYTE' x , y" :=
  (BOP OpSize1 OP_XOR (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.
Notation "'CMP' 'BYTE' x , y" :=
  (BOP OpSize1 OP_CMP (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)

(* This prevents two memory operands *)
Definition makeMOV dst (src: InstrSrc) :=
  match dst, src with
  | InstrArgR OpSize1 dst, InstrArgR OpSize1 src => MOVOP OpSize1 (DstSrcRR OpSize1 dst src)
  | InstrArgR OpSize2 dst, InstrArgR OpSize2 src => MOVOP OpSize2 (DstSrcRR OpSize2 dst src)
  | InstrArgR OpSize4 dst, InstrArgR OpSize4 src => MOVOP OpSize4 (DstSrcRR OpSize4 dst src)
  | InstrArgR OpSize8 dst, InstrArgR OpSize8 src => MOVOP OpSize8 (DstSrcRR OpSize8 dst src)

  | InstrArgR OpSize1 dst, InstrArgM src => MOVOP OpSize1 (DstSrcRM OpSize1 dst src)
  | InstrArgR OpSize2 dst, InstrArgM src => MOVOP OpSize2 (DstSrcRM OpSize2 dst src)
  | InstrArgR OpSize4 dst, InstrArgM src => MOVOP OpSize4 (DstSrcRM OpSize4 dst src) 
  | InstrArgR OpSize8 dst, InstrArgM src => MOVOP OpSize8 (DstSrcRM OpSize8 dst src) 

  | InstrArgR OpSize1 dst, ConstSrc n => MOVOP OpSize1 (DstSrcRI OpSize1 dst (low 8 n))
  | InstrArgR OpSize4 dst, ConstSrc n => MOVOP OpSize4 (DstSrcRI OpSize4 dst n)
  | InstrArgR OpSize8 dst, ConstSrc n => MOVOP OpSize8 (DstSrcRI OpSize8 dst n)
  | InstrArgR OpSize8 dst, QConstSrc n => MOVABS dst n

  | InstrArgM dst, InstrArgR OpSize1 src => MOVOP OpSize1 (DstSrcMR OpSize1 dst src)
  | InstrArgM dst, InstrArgR OpSize2 src => MOVOP OpSize2 (DstSrcMR OpSize2 dst src)
  | InstrArgM dst, InstrArgR OpSize4 src => MOVOP OpSize4 (DstSrcMR OpSize4 dst src)
  | InstrArgM dst, InstrArgR OpSize8 src => MOVOP OpSize8 (DstSrcMR OpSize8 dst src)

  | InstrArgM dst, ConstSrc n => MOVOP OpSize8 (DstSrcMI OpSize8 dst n)
  | _, _=> BADINSTR
  end.

Notation "'MOV' x , y" := (makeMOV x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOV' 'BYTE' x , y" :=
  (MOVOP OpSize1 (DstSrcMI OpSize1 x%ms y)) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    MOV operations
  ---------------------------------------------------------------------------*)

(* This forces exactly one xmm operand *)
Definition makeMOVQ dst (src : InstrSrc) :=
  match dst, src with
  | InstrArgXMM dst, InstrArgR OpSize8 src => MOVQ (XMMDstSrcXRM dst (XMemM (mkMemSpec (Some src, None) None)))
  | InstrArgXMM dst, InstrArgM src => MOVQ (XMMDstSrcXRM dst (XMemM src))
  | InstrArgR OpSize8 dst, InstrArgXMM src => MOVQ (XMMDstSrcRMX (XMemM (mkMemSpec (Some dst, None) None)) src)
  | InstrArgM dst, InstrArgXMM src => MOVQ (XMMDstSrcRMX (XMemM dst) src)
  | _, _ => BADINSTR
  end.

Notation "'MOVQ' x , y" := (makeMOVQ x y) (x,y at level 55, at level 60) : instr_scope.

Notation "'TEST' x , y"       := (TESTOP OpSize8  x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'TEST' 'BYTE' x , y":= (TESTOP OpSize1 x%ms y) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVZX' x , y" := (MOVX false _ x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.
Notation "'MOVSX' x , y" := (MOVX true _ x%ms y%ms) (x,y at level 55, at level 60) : instr_scope.

(*---------------------------------------------------------------------------
    Shift and rotate
  ---------------------------------------------------------------------------*)

Notation "'SAL' x , c" := (SHIFTOP _ OP_SAL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SAR' x , c" := (SHIFTOP _ OP_SAR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHL' x , c" := (SHIFTOP _ OP_SHL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'SHR' x , c" := (SHIFTOP _ OP_SHR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCL' x , c" := (SHIFTOP _ OP_RCL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'RCR' x , c" := (SHIFTOP _ OP_RCR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROL' x , c" := (SHIFTOP _ OP_ROL x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.
Notation "'ROR' x , c" := (SHIFTOP _ OP_ROR x%ms (ShiftCountI c)) (x, c at level 55, at level 60) : instr_scope.


Definition makeIMUL dst (src: InstrSrc)(c: option DWORD) :=
  match dst, src, c with
    | InstrArgR OpSize1 dst, InstrArgR OpSize1 src, None =>
      IMUL OpSize1 (ImulDstSrcRR OpSize1 dst src)
    | InstrArgR OpSize2 dst, InstrArgR OpSize2 src, None =>
      IMUL OpSize2 (ImulDstSrcRR OpSize2 dst src)
    | InstrArgR OpSize4 dst, InstrArgR OpSize4 src, None =>
      IMUL OpSize4 (ImulDstSrcRR OpSize4 dst src)
    | InstrArgR OpSize8 dst, InstrArgR OpSize8 src, None =>
      IMUL OpSize8 (ImulDstSrcRR OpSize8 dst src)

    | InstrArgR OpSize1 dst, InstrArgM src, None =>
      IMUL OpSize1 (ImulDstSrcRM OpSize1 dst src)
    | InstrArgR OpSize2 dst, InstrArgM src, None =>
      IMUL OpSize2 (ImulDstSrcRM OpSize2 dst src)
    | InstrArgR OpSize4 dst, InstrArgM src, None =>
      IMUL OpSize4 (ImulDstSrcRM OpSize4 dst src) 
    | InstrArgR OpSize8 dst, InstrArgM src, None =>
      IMUL OpSize8 (ImulDstSrcRM OpSize8 dst src) 

    | InstrArgR OpSize1 dst, InstrArgR OpSize1 src, Some c =>
      (* TODO: Are these 'low' legit? *)
      IMUL OpSize1 (ImulDstSrcRRI OpSize1 dst src (low 8 c))
    | InstrArgR OpSize2 dst, InstrArgR OpSize2 src, Some c =>
      (* TODO: Are these 'low' legit? *)
      IMUL OpSize2 (ImulDstSrcRRI OpSize2 dst src (low 16 c))
    | InstrArgR OpSize4 dst, InstrArgR OpSize4 src, Some c =>
      IMUL OpSize4 (ImulDstSrcRRI OpSize4 dst src c)
    | InstrArgR OpSize8 dst, InstrArgR OpSize8 src, Some c =>
      IMUL OpSize8 (ImulDstSrcRRI OpSize8 dst src c)

    | InstrArgR OpSize1 dst, InstrArgM src, Some c =>
      (* TODO: Are these 'low' legit? *)
      IMUL OpSize1 (ImulDstSrcRMI OpSize1 dst src (low 8 c))
    | InstrArgR OpSize2 dst, InstrArgM src, Some c =>
      (* TODO: Are these 'low' legit? *)
      IMUL OpSize2 (ImulDstSrcRMI OpSize2 dst src (low 16 c))
    | InstrArgR OpSize4 dst, InstrArgM src, Some c =>
      IMUL OpSize4 (ImulDstSrcRMI OpSize4 dst src c) 
    | InstrArgR OpSize8 dst, InstrArgM src, Some c =>
      IMUL OpSize8 (ImulDstSrcRMI OpSize8 dst src c) 
    | _, _, _=> BADINSTR
  end.


Notation "'IMUL' x , y" := (makeIMUL x y None) (x,y at level 55, at level 60) : instr_scope.
Notation "'IMUL' x , y , c" := (makeIMUL x%ms y%ms (Some c)) (x,y at level 55, at level 60) : instr_scope.

Notation "'LEA' x , y" := (LEA x (RegMemM OpSize4 y%ms)) (x,y at level 55, at level 60) : instr_scope.

Notation "'RET' x" := (RETOP x) (at level 60, x at level 55, format "'RET' x") : instr_scope.

Definition NOP := XCHG OpSize4 EAX (RegMemR OpSize4 EAX).

Arguments PUSH (src)%ms.
Arguments POP [s] (dst)%ms.

Notation "'SETA'"  := (SET CC_BE false) : instr_scope.
Notation "'SETAE'" := (SET CC_B  false) : instr_scope.
Notation "'SETAB'" := (SET CC_B  true)  : instr_scope.
Notation "'SETBE'" := (SET CC_BE true)  : instr_scope.
Notation "'SETC'"  := (SET CC_B  true)  : instr_scope.
Notation "'SETE'"  := (SET CC_Z true)   : instr_scope.
Notation "'SETG'"  := (SET CC_LE false) : instr_scope.
Notation "'SETGE'" := (SET CC_L false)  : instr_scope.
Notation "'SETL'"  := (SET CC_L true)   : instr_scope.
Notation "'SETLE'" := (SET CC_LE true)  : instr_scope.
Notation "'SETNA'" := (SET CC_BE true)  : instr_scope.
Notation "'SETNB'" := (SET CC_B false)  : instr_scope.
Notation "'SETNBE'":= (SET CC_BE false) : instr_scope.
Notation "'SETNC'" := (SET CC_B false)  : instr_scope.
Notation "'SETNE'" := (SET CC_Z false)  : instr_scope.
Notation "'SETNG'" := (SET CC_LE true)  : instr_scope.
Notation "'SETNGE'":= (SET CC_L true)   : instr_scope.
Notation "'SETNL'" := (SET CC_L false)  : instr_scope.
Notation "'SETNLE'":= (SET CC_LE false) : instr_scope.
Notation "'SETNO'" := (SET CC_O false)  : instr_scope.
Notation "'SETNP'" := (SET CC_P false)  : instr_scope.
Notation "'SETNS'" := (SET CC_S false)  : instr_scope.
Notation "'SETNZ'" := (SET CC_Z false)  : instr_scope.
Notation "'SETO'"  := (SET CC_O true)   : instr_scope.
Notation "'SETP'"  := (SET CC_P true)   : instr_scope.
Notation "'SETPE'" := (SET CC_P true)   : instr_scope.
Notation "'SETPO'" := (SET CC_P false)  : instr_scope.
Notation "'SETS'"  := (SET CC_S true)   : instr_scope.
Notation "'SETZ'"  := (SET CC_Z true)   : instr_scope.

(* Typical use: in "Eval showinstr in linearize p" *)
Declare Reduction showinstr := cbv beta delta -[fromNat makeMOV makeBOP] zeta iota.

Module Examples.
Open Scope memspec_scope.
Open Scope instr_scope.

Example ex1 := ADD EAX, [RBX + 3].
Example ex2 := INC BYTE [RCX + RDI*4 + 78].
Example ex3 (r:gpReg) := MOV RDI, [r].
Example ex4 (a:DWORD) := MOV RDI, [a].
Example ex5 (a:DWORD) := MOV RDI, a.
Example ex6 (r:BYTELReg) := MOV AL, r.
Example ex7 (r:gpReg) := POP [r + #x"0000001C"].
Example ex8 := CMP AL, (#c"!":BYTE).
Example ex9 := MOV DX, BP. 
Example ex10 := NOT [RBX + RDI*4 + 3]. 

Close Scope instr_scope.
End Examples.
