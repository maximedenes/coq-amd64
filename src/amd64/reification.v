From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq fintype tuple.
From CoqFFI Require Import reifiable reify coqFFI.
Require Import bitsops bitsrep reg instr instrsyntax reader writer program.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Encodable Decodable.

Reification for opsize.

Reification for UnaryOp.

Reification for gpReg.

Reification for BYTELReg.

Reification for WORDReg.

Reification for DWORDReg.

Instance encode_gpVReg s : Encodable.t (gpVReg s) := fun r =>
  match s return gpVReg s -> SExpr.t with
  | OpSize1 => fun r => encode r
  | OpSize2 => fun r => encode r
  | OpSize4 => fun r => encode r
  | OpSize8 => fun r => encode r
  end r.

Instance decode_gpVReg s : Decodable.t (gpVReg s) :=
  match s return SExpr.t -> option (gpVReg s) with
  | OpSize1 => fun e => decode e
  | OpSize2 => fun e => decode e
  | OpSize4 => fun e => decode e
  | OpSize8 => fun e => decode e
  end.

Reification for reg.

Reification for scale.

Instance encode_tuple T `{Encodable.t T} n : Encodable.t (n.-tuple T) :=
  fun t => encode (t : seq T).

Lemma altP P b : reflect P b -> alt_spec P b b.
Proof. by move=> Pb; case def_b: b / Pb; constructor; rewrite ?def_b. Defined.

Lemma idP {b1 : bool} : reflect b1 b1.
Proof. by case b1; constructor. Defined.

Lemma boolP (b1 : bool) : alt_spec b1 b1 b1.
Proof. exact: (altP idP). Defined.

Instance decode_tuple T `{Decodable.t T} n : Decodable.t (n.-tuple T) :=
  fun e => if decode e is Some s then
     if boolP (size s == n) is AltTrue p then Some (@Tuple n T s p)
     else None
  else None.

Reification for memspec.

Reification for regmem.

Reification for BinOp.

Reification for dstsrc.

Reification for BitOp.

Reification for regimm.

Reification for SSEreg.

Reification for XMMreg.

Reification for xmmdstsrc.

Reification for ShiftOp.

Reification for ShiftCount.

Reification for Condition.

Reification for Tgt.

Reification for src.

Reification for JmpTgt.

Reification for Instr.

Section hacks.

(** Programs we reify should not contain unresolved labels *)
Instance : Encodable.t (DWORD -> program) :=
  (fun _ => SExpr.I 1).

Instance : Decodable.t (DWORD -> program) :=
  (fun _ => None).

(** They shouldn't contain data either *)
(* Horrible hack *)

Instance : Encodable.t Type :=
  (fun _ => SExpr.I 1).

Instance : Decodable.t Type :=
  (fun _ => None).

Instance : forall T, Encodable.t (Reader T) :=
  fun _ _ => SExpr.I 1.

Instance : forall T, Decodable.t (Reader T) :=
  fun _ _ => None.

Instance : forall T, Encodable.t (Writer T) :=
  fun _ _ => SExpr.I 1.

Instance : forall T, Decodable.t (Writer T) :=
  fun _ _ => None.

Instance dangerous_encode T : Encodable.t T | 999999 :=
  fun _ => SExpr.I 1.

Instance dangerous_decode T : Decodable.t T | 999999 :=
  fun _ => None.

Reification for program.

End hacks.

(* Input for the printer *)
Definition import_input := @decode (list string * program)%type _.

(*
Definition encode_opsize (s : opsize) :=
  match s with
  | OpSize1 => Encode 0
  | OpSize2 => Encode 1
  | OpSize4 => Encode 2
  | OpSize8 => Encode 3
  end.

Definition error_opsize := OpSize1.

Definition decode_opsize (e : SExpr.t) :=
  match Decode e with
  | 0 => OpSize1
  | 1 => OpSize2
  | 2 => OpSize4
  | 3 => OpSize8
  | _ => error_opsize
  end.

Instance : Reifiable.t opsize := Reifiable.New encode_opsize decode_opsize.

Definition encode_UnaryOp (op : UnaryOp) :=
  match op with
  | OP_INC => Encode 0
  | OP_DEC => Encode 1
  | OP_NOT => Encode 2
  | OP_NEG => Encode 3
  end.

Definition error_UnaryOp := OP_INC.

Definition decode_UnaryOp (e : SExpr.t) :=
  match Decode e with
  | 0 => OP_INC
  | 1 => OP_DEC
  | 2 => OP_NOT
  | 3 => OP_NEG
  | _ => error_UnaryOp
  end.

Instance : Reifiable.t UnaryOp := Reifiable.New encode_UnaryOp decode_UnaryOp.

Definition encode_gpReg r :=
  match r with
  | RAX => Encode 0
  | RBX => Encode 1
  | RCX => Encode 2
  | RDX => Encode 3
  | RSI => Encode 4
  | RDI => Encode 5
  | RBP => Encode 6
  | RSP => Encode 7
  | R8 => Encode 8
  | R9 => Encode 9
  | R10 => Encode 10
  | R11 => Encode 11
  | R12 => Encode 12
  | R13 => Encode 13
  | R14 => Encode 14
  | R15 => Encode 15
  end.

Definition error_gpReg := RAX.

Definition decode_gpReg e :=
  match Decode e with
  | 0 => RAX
  | 1 => RBX
  | 2 => RCX
  | 3 => RDX
  | 4 => RSI
  | 5 => RDI
  | 6 => RBP
  | 7 => RSP
  | 8 => R8
  | 9 => R9
  | 10 => R10
  | 11 => R11
  | 12 => R12
  | 13 => R13
  | 14 => R14
  | 15 => R15
  | _ => error_gpReg
  end.

Instance : Reifiable.t gpReg := Reifiable.New encode_gpReg decode_gpReg.

Definition encode_BYTELReg r :=
  let 'mkByteLReg r := r in Encode r.

Definition decode_BYTELReg e :=
  mkByteLReg (Decode e).

Instance : Reifiable.t BYTELReg := Reifiable.New encode_BYTELReg decode_BYTELReg.

Definition encode_WORDReg r :=
  let 'mkWordReg r := r in Encode r.

Definition decode_WORDReg e :=
  mkWordReg (Decode e).

Instance : Reifiable.t WORDReg := Reifiable.New encode_WORDReg decode_WORDReg.

Definition encode_DWORDReg r :=
  let 'mkDWordReg r := r in Encode r.

Definition decode_DWORDReg e :=
  mkDWordReg (Decode e).

Instance : Reifiable.t DWORDReg := Reifiable.New encode_DWORDReg decode_DWORDReg.

Definition encode_gpVReg s (r : gpVReg s) :=
  match s return gpVReg s -> SExpr.t with
  | OpSize1 => fun r => Encode r
  | OpSize2 => fun r => Encode r
  | OpSize4 => fun r => Encode r
  | OpSize8 => fun r => Encode r
  end r.

Definition decode_gpVReg s e :=
  match s return SExpr.t -> gpVReg s with
  | OpSize1 => fun e => Decode e
  | OpSize2 => fun e => Decode e
  | OpSize4 => fun e => Decode e
  | OpSize8 => fun e => Decode e
  end e.

Instance : forall s, Reifiable.t (gpVReg s) :=
  fun s => Reifiable.New (@encode_gpVReg s) (@decode_gpVReg s).

Definition encode_scale s :=
  match s with
  | S1 => Encode 0
  | S2 => Encode 1
  | S4 => Encode 2
  | S8 => Encode 3
  end.

Definition error_scale := S1.

Definition decode_scale e :=
  match Decode e with
  | 0 => S1
  | 1 => S2
  | 2 => S4
  | 3 => S8
  | _ => error_scale
  end.

Instance : Reifiable.t scale := Reifiable.New encode_scale decode_scale.

Definition encode_reg r :=
  match r with
  | RIP => I
  | GPReg r => B I (Encode r)
  end.

Definition error_reg := RIP.

Definition decode_reg e :=
  match e with
  | I => RIP
  | B I e => GPReg (Decode e)
  | _ => error_reg
  end.

Definition encode_memspec ms :=
  let 'mkMemSpec ms off := ms in Reifiable.encode2 ms off.

Definition encode_regmem s (rm : regmem s) :=
  match rm with
  | RegMemR r => Encode r
  | RegMemM m => Encode m
  end.

Definition decode_opsize (e : SExpr.t) : opsize.
case: e.



Fixpoint encode_instr (i : Instr) :=
  match i with
  | UOP s uop rm => B (Encode 1)
  | _ => I
  end.

: forall s : opsize, UnaryOp -> regmem s -> Instr
  | BOP : forall s : opsize, BinOp -> dstsrc s -> Instr
  | BITOP : BitOp -> regmem OpSize4 -> reg.gpReg + BYTE -> Instr
  | TESTOP : forall s : opsize, regmem s -> regimm s -> Instr
  | MOVOP : forall s : opsize, dstsrc s -> Instr
  | MOVABS : reg.gpReg -> QWORD -> Instr
  | MOVX : bool -> forall s : opsize, reg.gpReg -> regmem s -> Instr
  | MOVQ : xmmdstsrc -> Instr
  | SHIFTOP : forall s : opsize, ShiftOp -> regmem s -> ShiftCount -> Instr
  | MUL : forall s : opsize, regmem s -> Instr
  | IMUL : forall s : opsize, reg.gpVReg s -> regmem s -> Instr
  | IMULimm : forall s : opsize, reg.gpVReg s -> regmem s -> VWORD s -> Instr
  | IDIV : forall s : opsize, regmem s -> Instr
  | LEA : reg.gpReg -> regmem OpSize4 -> Instr
  | XCHG : forall s : opsize, reg.gpVReg s -> regmem s -> Instr
  | JCCrel : Condition -> bool -> Tgt -> Instr
  | SET : Condition -> bool -> reg.gpVReg OpSize1 -> Instr
  | PUSH : src -> Instr
  | POP : regmem OpSize4 -> Instr
  | CALLrel : JmpTgt -> Instr
  | JMPrel : JmpTgt -> Instr
  | RETOP : WORD -> Instr
  | CQO : Instr
  | HLT : Instr
  | ENCLU : Instr
  | ENCLS : Instr
  | BADINSTR : Instr
  end.

Fixpoint encode_program (p : program) :=
  match p with
  | prog_instr i => B (Encode 0) (Export i)
  | prog_skip => B (Encode 1) I
  | p1;; p2 => B (Encode 2) (B (export_program p1) (export_program p2))
  | prog_declabel f => B (Encode 3) (export_program (f 0))
  | prog_label l => B (Encode 4) I
  | prog_data _ _ _ _ => B (Encode 5) I
  | prog_directive s => B (Encode 6) (Export s)
  end.
*)