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

Inductive nonSPReg := 
  RAX | RBX | RCX | RDX | RSI | RDI | RBP
| R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15.

Definition encode_nonSPReg r :=
  match r with
    | RAX => 0 | RCX => 1 | RDX => 2 | RBX => 3 | RBP => 5 | RSI => 6 | RDI => 7 
    | R8 => 8 | R9 => 9 | R10 => 10 | R11 => 11 | R12 => 12
    | R13 => 13 | R14 => 14 | R15 => 15
  end.
Lemma encode_nonSPReg_inj : injective encode_nonSPReg. Proof. by repeat case => //. Qed.
Canonical Structure nonSPRegEqMixin := InjEqMixin encode_nonSPReg_inj.
Canonical Structure nonSPReg_EqType := Eval hnf in EqType _ nonSPRegEqMixin.

(* General Purpose Registers *)

Inductive gpReg := mkGPReg (r: nonSPReg) :> gpReg | RSP.

Definition encode_gpReg r :=
  match r with
    | RSP => 4
    | mkGPReg r => encode_nonSPReg r
  end.
Lemma encode_gpReg_inj : injective encode_gpReg. Proof. by repeat case => //. Qed.
Canonical Structure gpRegEqMixin := InjEqMixin encode_gpReg_inj.
Canonical Structure gpReg_eqType := Eval hnf in EqType _ gpRegEqMixin.

Definition decode_gpReg n: option gpReg :=
  match n with
    | 0 => Some (RAX:gpReg)  | 1 => Some (RCX:gpReg)  | 2 => Some (RDX:gpReg)
    | 3 => Some (RBX:gpReg) | 4 => Some (RSP:gpReg)   | 5 => Some (RBP:gpReg)
    | 6 => Some (RSI:gpReg)  | 7 => Some (RDI:gpReg)  | 8 => Some (R8:gpReg)
    | 9 => Some (R9:gpReg)   | 10 => Some (R10:gpReg) | 11 => Some (R11:gpReg)
    | 12 => Some (R12:gpReg) | 13 => Some (R13:gpReg) | 14 => Some (R14:gpReg)
    | _ => None
  end.

(* All registers, including RIP but excluding RFL *)
Inductive reg := GPReg (r: gpReg) | RIP.

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
Inductive nonSPReg8 := mkNonSPReg8 (r: nonSPReg).
Inductive gpReg8 := mkGPReg8 (r: gpReg)  (*| AH | BH | CH | DH *).
Definition BYTELReg := gpReg8.

Definition NonSPReg8_base r8 := let: mkNonSPReg8 r := r8 in r.
Coercion NonSPReg8_to_gpReg8 (r: nonSPReg8): gpReg8 := mkGPReg8 (NonSPReg8_base r).

Lemma NonSPReg8_base_inj : injective NonSPReg8_base.
Proof. move => [x] [y] [/=E]. by subst. Qed.
Canonical Structure NonSPReg8_EqMixin := InjEqMixin NonSPReg8_base_inj.
Canonical Structure NonSPReg8_EqType := Eval hnf in EqType _ NonSPReg8_EqMixin.

Definition encode_gpReg8 r8 := 
  match r8 with mkGPReg8 r => encode_gpReg r end.
Lemma encode_gpReg8_inj : injective encode_gpReg8.
Proof. repeat case => //; case => //.  Qed. 
Canonical Structure GPReg8_EqMixin := InjEqMixin encode_gpReg8_inj.
Canonical Structure GPReg8_EqType := Eval hnf in EqType _ GPReg8_EqMixin.


Definition AL := (mkNonSPReg8 RAX).
Definition BL := (mkNonSPReg8 RBX).
Definition CL := (mkNonSPReg8 RCX).
Definition DL := (mkNonSPReg8 RDX).
Definition SIL := (mkNonSPReg8 RSI).
Definition DIL := (mkNonSPReg8 RDI).
Definition BPL := (mkNonSPReg8 RBP).
Definition R8L := (mkNonSPReg8 R8).
Definition R9L := (mkNonSPReg8 R9).
Definition R10L := (mkNonSPReg8 R10).
Definition R11L := (mkNonSPReg8 R11).
Definition R12L := (mkNonSPReg8 R12).
Definition R13L := (mkNonSPReg8 R13).
Definition R14L := (mkNonSPReg8 R14).
Definition R15L := (mkNonSPReg8 R15).
Definition SPL := (mkGPReg8 RSP).

(* High byte registers are not addressable with REX prefix *)
Inductive BYTEHReg := AH|BH|CH|DH.

(* 16-bit registers, wrapping underlying 64-bit registers *)
Inductive nonSPReg16 := mkNonSPReg16 (r: nonSPReg).
Inductive gpReg16 := mkGPReg16 (r: gpReg).
Inductive WORDReg := mkReg16 (r: reg).

Definition nonSPReg16_base r16 := let: mkNonSPReg16 r := r16 in r.
Coercion NonSPReg16_to_GPReg16 (r: nonSPReg16) := mkGPReg16 (nonSPReg16_base r).

Definition GPReg16_base r16 := let: mkGPReg16 r := r16 in r.
Coercion GPReg16_to_Reg16 (r: gpReg16) := mkReg16 (GPReg16_base r).

Definition Reg16_base r16 := let: mkReg16 r := r16 in r.

Lemma nonSPReg16_base_inj : injective nonSPReg16_base.
Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure nonSPReg16_EqMixin := InjEqMixin nonSPReg16_base_inj.
Canonical Structure nonSPReg16_EqType := Eval hnf in EqType _ nonSPReg16_EqMixin.

Lemma GPReg16_base_inj : injective GPReg16_base.
Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure GPReg16_EqMixin := InjEqMixin GPReg16_base_inj.
Canonical Structure GPReg16_EqType := Eval hnf in EqType _ GPReg16_EqMixin.

Lemma Reg16_base_inj : injective Reg16_base. Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure Reg16_EqMixin := InjEqMixin Reg16_base_inj.
Canonical Structure Reg16_EqType := Eval hnf in EqType _ Reg16_EqMixin.


Definition AX := (mkNonSPReg16 RAX).
Definition BX := (mkNonSPReg16 RBX).
Definition CX := (mkNonSPReg16 RCX).
Definition DX := (mkNonSPReg16 RDX).
Definition SI := (mkNonSPReg16 RSI).
Definition DI := (mkNonSPReg16 RDI).
Definition BP := (mkNonSPReg16 RBP).
Definition R8W := (mkNonSPReg16 R8).
Definition R9W := (mkNonSPReg16 R9).
Definition R10W := (mkNonSPReg16 R10).
Definition R11W := (mkNonSPReg16 R11).
Definition R12W := (mkNonSPReg16 R12).
Definition R13W := (mkNonSPReg16 R13).
Definition R14W := (mkNonSPReg16 R14).
Definition R15W := (mkNonSPReg16 R15).
Definition SP := (mkGPReg16 RSP).
Definition IP := (mkReg16 RIP).

(* 32-bit registers, wrapping underlying 64-bit registers *)
Inductive nonSPReg32 := mkNonSPReg32 (r: nonSPReg).
Inductive gpReg32 := mkGPReg32 (r: gpReg).
Inductive DWORDReg := mkReg32 (r: reg).

Definition nonSPReg32_base r32 := let: mkNonSPReg32 r := r32 in r.
Coercion NonSPReg32_to_GPReg32 (r: nonSPReg32): gpReg32 := mkGPReg32 (nonSPReg32_base r).
Definition gpReg32_base r32 := let: mkGPReg32 r := r32 in r.
Coercion gpReg32_to_Reg32 (r: gpReg32): DWORDReg := mkReg32 (gpReg32_base r).

Lemma NonSPReg32_base_inj : injective nonSPReg32_base.
Proof. move => [x] [y] [/=E]. by subst. Qed. 
Canonical Structure NonSPReg32_EqMixin := InjEqMixin NonSPReg32_base_inj.
Canonical Structure NonSPReg32_EqType := Eval hnf in EqType _ NonSPReg32_EqMixin.

Lemma GPReg32_base_inj : injective gpReg32_base. Proof. move => [x] [y] [/=E]. by subst. Qed.
Canonical Structure GPReg32_EqMixin := InjEqMixin GPReg32_base_inj.
Canonical Structure GPReg32_EqType := Eval hnf in EqType _ GPReg32_EqMixin.


Definition EAX := (mkNonSPReg32 RAX).
Definition EBX := (mkNonSPReg32 RBX).
Definition ECX := (mkNonSPReg32 RCX).
Definition EDX := (mkNonSPReg32 RDX).
Definition ESI := (mkNonSPReg32 RSI).
Definition EDI := (mkNonSPReg32 RDI).
Definition EBP := (mkNonSPReg32 RBP).
Definition R8D := (mkNonSPReg32 R8).
Definition R9D := (mkNonSPReg32 R9).
Definition R10D := (mkNonSPReg32 R10).
Definition R11D := (mkNonSPReg32 R11).
Definition R12D := (mkNonSPReg32 R12).
Definition R13D := (mkNonSPReg32 R13).
Definition R14D := (mkNonSPReg32 R14).
Definition R15D := (mkNonSPReg32 R15).
Definition ESP := (mkGPReg32 RSP).
Definition EIP := (mkReg32 RIP).


Definition nonSPVReg (s: opsize) := 
  match s with
    | OpSize1 => nonSPReg8
    | OpSize2 => nonSPReg16
    | OpSize4 => nonSPReg32
    | OpSize8 => nonSPReg
  end.

Definition gpVReg (s: opsize) := 
  match s with
    | OpSize1 => gpReg8
    | OpSize2 => gpReg16
    | OpSize4 => gpReg32
    | OpSize8 => gpReg
  end.

Definition vreg (s: opsize) :=
  match s with
    | OpSize1 => BYTELReg
    | OpSize2 => WORDReg
    | OpSize4 => DWORDReg
    | OpSize8 => reg
  end.

(*
Coercion RegToVReg (r: gpReg) : gpVReg OpSize8 := r.
Coercion DWORDRegToVReg (r:DWORDReg) : vreg OpSize4 := r.
Coercion WORDRegToVReg (r:WORDReg) : vreg OpSize2 := r.
Coercion BYTELRegToVReg (r:BYTELReg) : vreg OpSize1 := r.
Coercion AnyRegToVRegAny (r: reg) : vreg OpSize8 := r.
 *)

Coercion nonSPVReg_to_vreg {s} : nonSPVReg s -> vreg s  := 
  match s return nonSPVReg s -> vreg s with 
    | OpSize1 => fun r =>
                   match r with
                     | mkNonSPReg8 r => mkGPReg8 (mkGPReg r)
                   end
    | OpSize2 => fun r =>
                   match r with
                     | mkNonSPReg16 r => mkReg16 (mkGPReg r)
                   end
    | OpSize4 => fun r =>
                   match r with
                     | mkNonSPReg32 r => mkReg32 (mkGPReg r)
                   end
    | OpSize8 => fun r => r
  end. 

Coercion gpVReg_to_vreg {s} : gpVReg s -> vreg s  := 
  match s return gpVReg s -> vreg s with 
    | OpSize1 => fun r => r
    | OpSize2 => fun r =>
                   match r with
                     | mkGPReg16 r => mkReg16 r
                   end
    | OpSize4 => fun r =>
                   match r with
                     | mkGPReg32 r => mkReg32 r
                   end
    | OpSize8 => fun r => r
  end. 



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
Notation XMM11 := (mkXMMreg YMM11).
Notation XMM12 := (mkXMMreg YMM12).
Notation XMM13 := (mkXMMreg YMM13).
Notation XMM14 := (mkXMMreg YMM14).
Notation XMM15 := (mkXMMreg YMM15).

Definition XMMreg_toNat r :=
  (* TODO: don't think is correct wrt. the encoding *)
  match r with XMM0 => 0 | XMM1 => 1 | XMM2 => 2 | XMM3 => 3 | XMM4 => 4
            | XMM5 => 5 | XMM6 => 6 | XMM7 => 7 
            | XMM8 => 8 | XMM9 => 9 | XMM10 => 10 | XMM11 => 11
            | XMM12 => 12 | XMM13 => 13 | XMM14 => 14 | XMM15 => 15 end.
Lemma XMMreg_toNat_inj : injective XMMreg_toNat. Proof. by repeat case => //. Qed.
Canonical Structure XMMreg_EqMixin := InjEqMixin XMMreg_toNat_inj.
Canonical Structure XMMreg_EqType := Eval hnf in EqType _ XMMreg_EqMixin.
