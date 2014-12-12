(*===========================================================================
    Model for x86 registers
    Note that the RFL register (flags) is treated separately.

    These are registers as used inside instructions, and can refer to
    overlapping sections of the real machine state e.g. AL, AH, AX, EAX
  ===========================================================================*)
From Ssreflect Require Import ssreflect ssrfun ssrbool.
From Ssreflect Require Import eqtype ssrnat seq choice.
From Ssreflect Require Import fintype tuple.
Require Import bitsrep.

(* TODO: check that RSP can be used as an index register on x86-64 with  *)
(* REX.X = 1 and index = 0100 in SIB, although GNU AS doesn't seem to *)
(* accept it. *)

(* General Purpose Registers *)
Inductive gpReg := RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP | R8 | R9
               | R10 | R11 | R12 | R13 | R14 | R15.

Definition encode_gpReg r :=
  match r with
  | RAX => 0  | RBX => 3  | RCX => 1  | RDX => 2  | RSI => 6  | RDI => 7
  | RSP => 4  | RBP => 5  | R8 => 8   | R9 => 9  | R10 => 10 | R11 => 11
  | R12 => 12 | R13 => 13 | R14 => 14 | R15 => 15
  end.

Lemma encode_gpReg_inj : injective encode_gpReg.
Proof. by case => //; case => //. Qed.

Canonical Structure gpRegEqMixin := InjEqMixin encode_gpReg_inj.
Canonical Structure gpReg_eqType := Eval hnf in EqType _ gpRegEqMixin.

Definition decode_gpReg n :=
  match n with
  | 0 => Some RAX  | 1 => Some RCX  | 2 => Some RDX  | 3 => Some RBX
  | 4 => Some RSP  | 5 => Some RBP  | 6 => Some RSI  | 7 => Some RDI
  | 8 => Some R8   | 9 => Some R9   | 10 => Some R10 | 11 => Some R11
  | 12 => Some R12 | 13 => Some R13 | 14 => Some R14 | _ => None
  end.

(* All registers, including RIP but excluding RFL *)
Inductive reg := GPReg (r : gpReg) | RIP.

Coercion GPReg : gpReg >-> reg.

(* RIP has (arbitrary) code 16 *)
Definition encode_reg r :=
  if r is GPReg r then encode_gpReg r else 16.

Lemma encode_reg_inj : injective encode_reg.
Proof.
by case => //; case => //; case => //; case => //; case => //; case => //.
Qed.

Canonical Structure regEqMixin := InjEqMixin encode_reg_inj.
Canonical Structure reg_eqType := Eval hnf in EqType _ regEqMixin.

(* Segment registers *)
Inductive segReg := CS | FS | GS.

Definition encode_segReg r :=
  match r with CS => 0 | FS => 1 | GS => 2 end.

Lemma encode_segReg_inj : injective encode_segReg.
Proof. by case; case. Qed.
Canonical Structure segRegEqMixin := InjEqMixin encode_segReg_inj.
Canonical Structure segReg_eqType := Eval hnf in EqType _ segRegEqMixin.

(* Low byte registers, wrapping underlying 64-bit registers *)
Inductive BYTELReg := mkByteLReg (r : gpReg).
Notation AL := (mkByteLReg RAX).
Notation BL := (mkByteLReg RBX).
Notation CL := (mkByteLReg RCX).
Notation DL := (mkByteLReg RDX).
Notation SIL := (mkByteLReg RSI).
Notation DIL := (mkByteLReg RDI).
Notation BPL := (mkByteLReg RBP).
Notation SPL := (mkByteLReg RSP).
Notation R8B := (mkByteLReg R8).
Notation R9B := (mkByteLReg R9).
Notation R10B := (mkByteLReg R10).
Notation R11B := (mkByteLReg R11).
Notation R12B := (mkByteLReg R12).
Notation R13B := (mkByteLReg R13).
Notation R14B := (mkByteLReg R14).
Notation R15B := (mkByteLReg R15).

(* High byte registers are not addressable with REX prefix *)
Inductive BYTEHReg := AH|BH|CH|DH.

(* 16-bit registers, wrapping underlying 64-bit registers *)
Inductive WORDReg := mkWordReg (r : gpReg).
Notation AX := (mkWordReg RAX).
Notation BX := (mkWordReg RBX).
Notation CX := (mkWordReg RCX).
Notation DX := (mkWordReg RDX).
Notation SI := (mkWordReg RSI).
Notation DI := (mkWordReg RDI).
Notation BP := (mkWordReg RBP).
Notation SP := (mkWordReg RSP).
Notation R8W := (mkWordReg R8).
Notation R9W := (mkWordReg R9).
Notation R10W := (mkWordReg R10).
Notation R11W := (mkWordReg R11).
Notation R12W := (mkWordReg R12).
Notation R13W := (mkWordReg R13).
Notation R14W := (mkWordReg R14).
Notation R15W := (mkWordReg R15).

(* 32-bit registers, wrapping underlying 64-bit registers *)
Inductive DWORDReg := mkDWordReg (r : gpReg).
Notation EAX := (mkDWordReg RAX).
Notation EBX := (mkDWordReg RBX).
Notation ECX := (mkDWordReg RCX).
Notation EDX := (mkDWordReg RDX).
Notation ESI := (mkDWordReg RSI).
Notation EDI := (mkDWordReg RDI).
Notation EBP := (mkDWordReg RBP).
Notation ESP := (mkDWordReg RSP).
Notation R8D := (mkDWordReg R8).
Notation R9D := (mkDWordReg R9).
Notation R10D := (mkDWordReg R10).
Notation R11D := (mkDWordReg R11).
Notation R12D := (mkDWordReg R12).
Notation R13D := (mkDWordReg R13).
Notation R14D := (mkDWordReg R14).
Notation R15D := (mkDWordReg R15).

Definition gpVReg (s: opsize) :=
  match s with
  | OpSize1 => BYTELReg
  | OpSize2 => WORDReg
  | OpSize4 => DWORDReg
  | OpSize8 => gpReg
  end.

Definition vreg (s: opsize) :=
  match s with
  | OpSize1 => BYTELReg
  | OpSize2 => WORDReg
  | OpSize4 => DWORDReg
  | OpSize8 => reg
  end.

Coercion RegToVReg (r: gpReg) : gpVReg OpSize8 := r.
Coercion DWORDRegToVReg (r:DWORDReg) : gpVReg OpSize4 := r.
Coercion WORDRegToVReg (r:WORDReg) : gpVReg OpSize2 := r.
Coercion BYTELRegToVReg (r:BYTELReg) : gpVReg OpSize1 := r.
Coercion AnyRegToVRegAny (r: reg) : vreg OpSize8 := r.

Inductive SSEreg := YMM0 | YMM1 | YMM2  | YMM3  | YMM4  | YMM5  | YMM6 | YMM7
                  | YMM8 | YMM9 | YMM10 | YMM11 | YMM12 | YMM13 | YMM14 | YMM15.

Inductive XMMreg := mkXMMreg (r : SSEreg).

Notation XMM0 := (mkXMMreg YMM0).
Notation XMM1 := (mkXMMreg YMM1).
Notation XMM2 := (mkXMMreg YMM2).
Notation XMM3 := (mkXMMreg YMM3).
Notation XMM4 := (mkXMMreg YMM4).
Notation XMM5 := (mkXMMreg YMM5).
Notation XMM6 := (mkXMMreg YMM6).
Notation XMM7 := (mkXMMreg YMM7).
Notation XMM8 := (mkXMMreg YMM8).
Notation XMM9 := (mkXMMreg YMM9).
Notation XMM10 := (mkXMMreg YMM10).
Notation XMM11 := (mkXMMreg YMM1).
Notation XMM12 := (mkXMMreg YMM12).
Notation XMM13 := (mkXMMreg YMM13).
Notation XMM14 := (mkXMMreg YMM14).
Notation XMM15 := (mkXMMreg YMM15).