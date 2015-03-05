(*======================================================================================
  Instruction codec
  ======================================================================================*)
From Ssreflect
    Require Import ssreflect ssrfun seq ssrbool ssrnat fintype eqtype tuple.
From Coq
     Require Import Strings.String.
Require Import bitsrep.
Require Import cast codec bitscodec.
Require Import instr encdechelp reg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Casts for datatypes used in instructions
  ---------------------------------------------------------------------------*)
Definition unSrcR : CAST (gpReg) (src).
apply: MakeCast SrcR (fun src => if src is SrcR r then Some r else None) _.
by elim; congruence. Defined.

Definition unSrcI : CAST DWORD src.
apply: MakeCast SrcI (fun s => if s is SrcI i then Some i else None) _.
by elim; congruence. Defined.

Definition unRegMemR d : CAST (gpVReg d) (regmem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmR d : CAST (gpVReg d) (regimm d).
apply: MakeCast (RegImmR d) (fun rm => if rm is RegImmR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmI d : CAST (IMM d) (regimm d).
apply: MakeCast (RegImmI d) (fun rm => if rm is RegImmI v then Some v else None) _.
by elim; congruence. Defined.

Definition unJmpTgtI : CAST Tgt JmpTgt.
apply: (MakeCast JmpTgtI (fun t => if t is JmpTgtI d then Some d else None) _).
elim; elim; congruence. Defined.

Definition unJmpTgtRM : CAST (regmem OpSize8) JmpTgt.
  refine (MakeCast (fun rm: regmem OpSize8 => match rm with
                                | RegMemR r => JmpTgtR (GPReg r)
                                | RegMemM m => JmpTgtM m
                                              end)
                   (fun i => match i with
                               | JmpTgtR (GPReg r) => Some (RegMemR OpSize8 r)
                               | JmpTgtM m => Some (RegMemM OpSize8 m)
                               | _ => None end) _).
  case=> x; case=> y; try case: x;  congruence.
Defined.

Definition unTgt : CAST (VWORD OpSize8) Tgt.
apply: (MakeCast mkTgt (fun t => let: mkTgt d := t in Some d) _).
by move => [d] y [<-].
Defined.

Definition unSrcRM : CAST (regmem OpSize8) src.
  refine (MakeCast
            (fun (rm: regmem OpSize8) =>
               match rm with
                 | RegMemR r => SrcR r
                 | RegMemM m => SrcM m
               end)
            (fun i =>
               match i with
                 | SrcR r => Some (RegMemR OpSize8 r)
                 | SrcM m => Some (RegMemM _ m)
                 | _ => None
               end) _).
  case=> x //; case=> y //; congruence. 
Defined.

(*---------------------------------------------------------------------------
    Casts and codecs for bit-encoded types e.g. registers, scales, conditions
  ---------------------------------------------------------------------------*)

(* 32-bit register encoding, including ESP *)
Definition GPReg32Codec (rexBit:bool) : Codec gpReg32 :=
if rexBit then
    #b"000" .$ always (R8D:gpReg32)
||| #b"001" .$ always (R9D:gpReg32)
||| #b"010" .$ always (R10D:gpReg32)
||| #b"011" .$ always (R11D:gpReg32)
||| #b"100" .$ always (R12D:gpReg32)
||| #b"101" .$ always (R13D:gpReg32)
||| #b"110" .$ always (R14D:gpReg32)
||| #b"111" .$ always (R15D:gpReg32)
else
    #b"000" .$ always (EAX:gpReg32)
||| #b"001" .$ always (ECX:gpReg32)
||| #b"010" .$ always (EDX:gpReg32)
||| #b"011" .$ always (EBX:gpReg32)
||| #b"100" .$ always ESP
||| #b"110" .$ always (ESI:gpReg32)
||| #b"111" .$ always (EDI:gpReg32)
||| #b"101" .$ always (EBP:gpReg32).

(* 64-bit register encoding, including RSP *)
Definition GPReg64Codec (rexBit:bool) : Codec gpReg :=
if rexBit then 
    #b"000" .$ always (R8:gpReg)
||| #b"001" .$ always (R9:gpReg)
||| #b"010" .$ always (R10:gpReg)
||| #b"011" .$ always (R11:gpReg)
||| #b"100" .$ always (R12:gpReg)
||| #b"101" .$ always (R13:gpReg)
||| #b"110" .$ always (R14:gpReg)
||| #b"111" .$ always (R15:gpReg)
else
    #b"000" .$ always (RAX:gpReg)
||| #b"001" .$ always (RCX:gpReg)
||| #b"010" .$ always (RDX:gpReg)
||| #b"011" .$ always (RBX:gpReg)
||| #b"100" .$ always RSP
||| #b"110" .$ always (RSI:gpReg)
||| #b"111" .$ always (RDI:gpReg)
||| #b"101" .$ always (RBP:gpReg).
  
(* Non-SP, 16-bit register encoding *)
Definition NonSPReg16Codec (rexBit:bool) : Codec nonSPReg16 :=
if rexBit then
    #b"000" .$ always R8W
||| #b"001" .$ always R9W
||| #b"010" .$ always R10W
||| #b"011" .$ always R11W
||| #b"100" .$ always R12W
||| #b"101" .$ always R13W
||| #b"110" .$ always R14W
||| #b"111" .$ always R15W
else
    #b"000" .$ always AX
||| #b"001" .$ always CX
||| #b"010" .$ always DX
||| #b"011" .$ always BX
||| #b"110" .$ always SI
||| #b"111" .$ always DI
||| #b"101" .$ always BP.

Definition opCast : CAST (BITS 3) BinOp.
apply: MakeCast (fun x => decBinOp x) (fun x => Some (encBinOp x)) _.
move => x y [<-]; by rewrite encBinOpK. Defined.
Definition opCodec    : Codec BinOp   := bitsCodec 3 ~~> opCast.

Definition shiftOpCast : CAST (BITS 3) ShiftOp.
apply: MakeCast (fun x => decShiftOp x) (fun x => Some (encShiftOp x)) _.
move => x y [<-]; by rewrite encShiftOpK. Defined.
Definition shiftOpCodec : Codec ShiftOp   := bitsCodec 3 ~~> shiftOpCast.

Definition bitOpCast : CAST (BITS 2) BitOp.
apply: MakeCast (fun x => decBitOp x) (fun x => Some (encBitOp x)) _.
move => x y [<-]; by rewrite encBitOpK. Defined.
Definition bitOpCodec : Codec BitOp   := bitsCodec 2 ~~> bitOpCast.

(* Index register in an SIB byte. 
   The X bit comes from the (optional) REX prefix in 64-bit mode.
   See Section 2.2.1.2, also table 2-5 *)

Definition SIBIxReg64Codec X : Codec (option ixReg) :=
if X
then
    #b"000" .$ always (Some R8)
||| #b"001" .$ always (Some R9)
||| #b"010" .$ always (Some R10)
||| #b"011" .$ always (Some R11)
||| #b"100" .$ always (Some R12)
||| #b"101" .$ always (Some R13)
||| #b"110" .$ always (Some R14)
||| #b"111" .$ always (Some R15)
else
    #b"000" .$ always (Some RAX)
||| #b"001" .$ always (Some RCX)
||| #b"010" .$ always (Some RDX)
||| #b"011" .$ always (Some RBX)
||| #b"100" .$ always None
||| #b"110" .$ always (Some RSI)
||| #b"111" .$ always (Some RDI)
||| #b"101" .$ always (Some RBP).

Definition SIBIxRegCodec X : Codec (option ixReg) :=
  SIBIxReg64Codec X.

(* This isn't quite right as EBP can't be used as a base with mod 00 - see table 2-3 *)
Definition SIBBaseRegCodec X : Codec baseReg :=
  GPReg64Codec X.


(* Can't encode R12 or R13 this way - see Table 2-5 *)

Definition NonBPNonSPBaseReg64Codec B : Codec baseReg :=
if B then
    #b"000" .$ always (R8: baseReg)
||| #b"001" .$ always (R9: baseReg)
||| #b"010" .$ always (R10: baseReg)
||| #b"011" .$ always (R11: baseReg)
||| #b"110" .$ always (R14: baseReg)
||| #b"111" .$ always (R15: baseReg)
else
    #b"000" .$ always (RAX: baseReg)
||| #b"001" .$ always (RCX: baseReg)
||| #b"010" .$ always (RDX: baseReg)
||| #b"011" .$ always (RBX: baseReg)
||| #b"110" .$ always (RSI: baseReg)
||| #b"111" .$ always (RDI: baseReg)
.

Definition NonBPBaseReg64Codec B : Codec baseReg :=
  NonBPNonSPBaseReg64Codec B
||| #b"100" .$ always RSP.

Definition NonBPNonSPBaseRegCodec B : Codec baseReg :=
  NonBPNonSPBaseReg64Codec B.

Definition NonBPBaseRegCodec B : Codec baseReg :=
  NonBPBaseReg64Codec B.

Definition NonSPBaseReg64Codec B : Codec baseReg :=
if B then
    #b"000" .$ always (R8: baseReg)
||| #b"001" .$ always (R9: baseReg)
||| #b"010" .$ always (R10: baseReg)
||| #b"011" .$ always (R11: baseReg)
||| #b"101" .$ always (R13: baseReg)
||| #b"110" .$ always (R14: baseReg)
||| #b"111" .$ always (R15: baseReg)
else
    #b"000" .$ always (RAX: baseReg)
||| #b"001" .$ always (RCX: baseReg)
||| #b"010" .$ always (RDX: baseReg)
||| #b"011" .$ always (RBX: baseReg)
||| #b"101" .$ always (RBP: baseReg)
||| #b"110" .$ always (RSI: baseReg)
||| #b"111" .$ always (RDI: baseReg)
.

Definition NonSPBaseRegCodec B : Codec baseReg :=
  NonSPBaseReg64Codec B.

Definition Reg8Codec (rexBit:bool): Codec gpReg8 := 
if rexBit then
    #b"000" .$ always (R8L:gpReg8)
||| #b"001" .$ always (R9L:gpReg8)
||| #b"010" .$ always (R10L:gpReg8)
||| #b"011" .$ always (R11L:gpReg8)
||| #b"100" .$ always (R12L:gpReg8)
||| #b"101" .$ always (R13L:gpReg8)
||| #b"110" .$ always (R14L:gpReg8)
||| #b"111" .$ always (R15L:gpReg8)
else
    #b"000" .$ always (AL:gpReg8)
||| #b"001" .$ always (CL:gpReg8)
||| #b"010" .$ always (DL:gpReg8)
||| #b"011" .$ always (BL:gpReg8)
(*||| #b"100" .$ always AH
||| #b"101" .$ always CH
||| #b"110" .$ always DH
||| #b"111" .$ always BH *).

Definition GPReg16Codec (rexBit:bool) : Codec gpReg16 := 
if rexBit then
    #b"000" .$ always (R8W:gpReg16)
||| #b"001" .$ always (R9W:gpReg16)
||| #b"010" .$ always (R10W:gpReg16)
||| #b"011" .$ always (R11W:gpReg16)
||| #b"100" .$ always (R12W:gpReg16)
||| #b"101" .$ always (R13W:gpReg16)
||| #b"110" .$ always (R14W:gpReg16)
||| #b"111" .$ always (R15W:gpReg16)
else
    #b"000" .$ always (AX:gpReg16)
||| #b"001" .$ always (CX:gpReg16)
||| #b"010" .$ always (DX:gpReg16)
||| #b"011" .$ always (BX:gpReg16)
||| #b"100" .$ always SP
||| #b"101" .$ always (BP:gpReg16)
||| #b"110" .$ always (SI:gpReg16)
||| #b"111" .$ always (DI:gpReg16).

Definition VRegCodec rexBit s : Codec (gpVReg s) :=
  match s return Codec (gpVReg s) with
  | OpSize1 => Reg8Codec rexBit
  | OpSize2 => GPReg16Codec rexBit
  | OpSize4 => GPReg32Codec rexBit
  | OpSize8 => GPReg64Codec rexBit
  end.

Definition VWORDCodec s : Codec (VWORD s) :=
  match s return Codec (VWORD s) with
  | OpSize1 => BYTECodec
  | OpSize2 => WORDCodec
  | OpSize4 => DWORDCodec
  | OpSize8 => QWORDCodec
  end.

Definition IMMCodec s : Codec (IMM s) :=
  match s with
  | OpSize1 => BYTECodec
  | OpSize2 => WORDCodec
  | OpSize4 => DWORDCodec
  | OpSize8 => DWORDCodec
  end.

Definition scaleCast : CAST (BITS 2) scale.
apply: MakeCast decScale (fun x => Some (encScale x)) _.
move => x y [<-]; by rewrite encScaleK. Defined.
Definition scaleCodec : Codec scale := bitsCodec 2 ~~> scaleCast.

Definition conditionCast : CAST (BITS 3) Condition.
apply: MakeCast decCondition (fun x => Some (encCondition x)) _.
move => x y [<-]; by rewrite encConditionK. Defined.
Definition conditionCodec : Codec Condition := bitsCodec 3 ~~> conditionCast.

Definition SIBCast : CAST (scale * option ixReg * option baseReg) (option baseReg * option (ixReg * scale)).
apply: MakeCast (fun p => let: (sc,o,r) := p
                 in (r, if o is Some ix then Some(ix,sc) else None))
                (fun p => let: (base, o) := p
                 in if o is Some(ix,sc) then Some(sc, Some ix, base)
                                        else Some(S1, None, base)) _.
move => [r' o'] [[sc o] r].
case: o' => //.
+ by move => [? ?] [-> <- ->].
+ by move => [<- <- <-].
Defined.

(* The X and B bits come from the (optional) REX prefix in 64-bit mode.
   See Section 2.2.1.2 *)
Definition SIBCodec X B := 
  scaleCodec $ SIBIxRegCodec X $ (SIBBaseRegCodec B ~~> unSome) ~~> SIBCast.  

Definition SIB00Codec X B := 
  scaleCodec $ SIBIxRegCodec X $ (NonBPBaseRegCodec B ~~> unSome) ~~> SIBCast.

Definition SIB00NoBaseCodec X :=
  scaleCodec $ SIBIxRegCodec X $ #b"101" .$ alwaysNone ~~> SIBCast.

(*
Definition tryEqAdSize F (a1 a2: AdSize): F a1 -> option (F a2) :=
  match a1, a2 with
  | AdSize4, AdSize4 => fun x => Some x
  | AdSize8, AdSize8 => fun x => Some x
  | _, _ => fun x => None
  end. 
 *)

Definition RIPrelCast s : CAST DWORD (regmem s).
  apply: (MakeCast
            (fun offset => RegMemM s (RIPrel offset))
            (fun rm => if rm is RegMemM (RIPrel offset)
                       then Some offset else None) _).
do 2 elim => //; by move => ? ? [->]. 
Defined. 

Definition mkMemSpecCast s : 
  CAST (option baseReg * option (ixReg * scale) * DWORD) (regmem s).
  apply: 
  (MakeCast (fun p => let: (b,i,d) := p in RegMemM s (mkMemSpec (b, i) (Some d)))
  (fun rm => if rm is RegMemM (mkMemSpec (b, i) (Some d))
             then Some (b,i,d) 
             else None ) _).
  case=> //; case=> //; case=> // a b;
    case=> // offset; case=> //; case=> //;
    by congruence. 
Defined. 

(* See Table 2-2 and 2-3 for details *)
Definition RegMemCodec T (R X B:bool) (regOrOpcodeCodec : Codec T) s : Codec (T * regmem s) :=

(* RIP-relative addressing. See Table 2-7 *)
(* NOTE: in 32-bit mode this is used for pure displacement *)
    #b"00" .$ regOrOpcodeCodec $ #b"101" .$ (DWORDCodec ~~> RIPrelCast s)

(* Mod R/M with mod=00: no displacement *)
||| #b"00" .$ regOrOpcodeCodec $ ((NonBPNonSPBaseRegCodec B ~~> unSome) $ alwaysNone $ always #0 ~~> mkMemSpecCast s)
(* SIB with mod=00: no displacement *)
||| #b"00" .$ regOrOpcodeCodec $ (#b"100" .$ SIB00Codec X B $ always #0 ~~> mkMemSpecCast s)
||| #b"00" .$ regOrOpcodeCodec $ (#b"100" .$ SIB00NoBaseCodec X $ DWORDCodec ~~> mkMemSpecCast s)

(* Mod R/M with mod=01: disp8 *)
||| #b"01" .$ regOrOpcodeCodec $ ((NonSPBaseRegCodec B ~~> unSome) $ alwaysNone $ shortDWORDCodec ~~> mkMemSpecCast s)
(* SIB with mod=01: disp8 *)
||| #b"01" .$ regOrOpcodeCodec $ (#b"100" .$ SIBCodec X B $ shortDWORDCodec ~~> mkMemSpecCast s)

(* Mod R/M with mod=10: disp32 *)
||| #b"10" .$ regOrOpcodeCodec $ ((NonSPBaseRegCodec B ~~> unSome) $ alwaysNone $ DWORDCodec ~~> mkMemSpecCast s)
(* SIB with mod=10: disp32 *)
||| #b"10" .$ regOrOpcodeCodec $ (#b"100" .$ SIBCodec X B $ DWORDCodec ~~> mkMemSpecCast s )

(* Mod R/M with mod=11: reg-reg *)
||| #b"11" .$ regOrOpcodeCodec $ (VRegCodec B s ~~> unRegMemR s).





Definition RegMemOpCodec R X B (op: BITS 3) dword :=
  RegMemCodec R X B (Const op) dword ~~> sndUnitCast _.

Definition mkOpSize p W b := 
  if b then
    if W then OpSize8 else if p then OpSize2 else OpSize4 
  else OpSize1.

Definition unDstSrcRMR s : CAST (gpVReg s * regmem s) (dstsrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s p.1 y
                              | RegMemM y => DstSrcRM s p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM x y => Some (x,RegMemM _ y)
                              | _ => None end) _).
elim => //.  
- by move => ? ? [? ?] [<- <-]. 
- by move => ? ? [? ?] [<-] [<-]. 
Defined. 

Definition unDstSrcMRR s : CAST (gpVReg s * regmem s) (dstsrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s y p.1
                              | RegMemM y => DstSrcMR s y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR x y => Some (y, RegMemM _ x)
                              | _ => None end) _).
elim => //. 
- by move => ? ? [? ?] [<-] <-. 
- by move => ? ? [? ?] [<- <-]. 
Defined.

Definition unDstSrcMRI s : CAST (regmem s * IMM s) (dstsrc s).
apply: (MakeCast
       (fun p => match p.1 with RegMemR y => (DstSrcRI s y p.2)
                              | RegMemM y => (DstSrcMI s y p.2) end)
       (fun ds => match ds with DstSrcRI x y => Some (RegMemR _ x, y)
                              | DstSrcMI x y => Some (RegMemM _ x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? [<- ->]. Defined.

Definition unDstSrcRI s : CAST (gpVReg s * IMM s) (dstsrc s).
apply: (MakeCast (fun p => DstSrcRI _ p.1 p.2)
       (fun ds => match ds with DstSrcRI x y => Some (x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. Defined.

(*
TODO: we have remove MovDstSrc 

Definition unMovDstSrcRMR s : CAST (gpVReg s * regmem s) (MovDstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => MovDstSrcRR s p.1 y
                              | RegMemM a y => MovDstSrcRM s a p.1 y end)
       (fun ds => match ds with MovDstSrcRR x y => Some (x,RegMemR _ y)
                              | MovDstSrcRM a x y => Some (x,RegMemM _ a y)
                              | _ => None end) _).
elim => //.  
- by move => ? ? [? ?] [<- <-]. 
- by move => ? ? ? [? ?] [<-] [<-]. 
Defined. 

Definition unMovDstSrcMRR s : CAST (GPReg s * RegMem s) (MovDstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => MovDstSrcRR s y p.1
                              | RegMemM a y => MovDstSrcMR s a y p.1 end)
       (fun ds => match ds with MovDstSrcRR x y => Some (y, RegMemR _ x)
                              | MovDstSrcMR a x y => Some (y, RegMemM _ a x)
                              | _ => None end) _).
elim => //. 
- by move => ? ? [? ?] [<-] <-. 
- by move => ? ? ? [? ?] [<- <-]. 
Defined.

(*
Definition unMovDstSrcMRI s : CAST (RegMem s * VWORD s) (MovDstSrc s).
eapply (MakeCast
       (fun p => match p.1 with RegMemR y => (MovDstSrcRI s y p.2)
                              | RegMemM a y => (MovDstSrcMI s a y p.2) end)
       (fun ds => match ds with MovDstSrcRI x y => Some (RegMemR _ x, y)
                              | MovDstSrcMI a x y => Some (RegMemM _ a x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? ? [<- ->]. Defined.
*)

Definition unMovDstSrcRI s : CAST (GPReg s * VWORD s) (MovDstSrc s).
  admit.
  (*
apply: (MakeCast (fun p => MovDstSrcRI _ p.1 p.2)
       (fun ds => match ds with MovDstSrcRI x y => Some (x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. *) Defined.
*)
(*---------------------------------------------------------------------------
    Casts for instructions
  ---------------------------------------------------------------------------*)
Definition prefAndOpSizeToBool (w: bool) (os: opsize) :=  
  match os, w with
  | OpSize4, false => Some true
  | OpSize2, true => Some true
  | OpSize1, _ => Some false  
  | _, _ => None
  end.

Definition sizesPrefixCodec X (c : bool -> bool -> Codec X) : Codec X :=
    #x"66" .$ (c true false)
||| #x"F3" .$ (c false true)
||| c false false.

Definition opSizePrefixCodec X (c : bool -> Codec X) : Codec X :=
    #x"66" .$ (c true)
||| c false.

(* We do not support 32bit addressing in 64 bits 
Definition adSizePrefixCodec X (c : AdSize -> Codec X) : Codec X :=
    #x"67" .$ (c AdSize4)
||| c AdSize8.
*)

(* REX prefix format, as described in section 2.2.1.2 *)
Definition rexPrefixCodec X (c: bool -> bool -> bool -> bool -> Codec X) : Codec X :=
    #b"0100" .$ Cond (fun W => Cond (fun R => Cond (fun X => Cond (fun B =>
    c W R X B))))
||| c false false false false.

(* We do not support segmentation
Definition segPrefixCodec X (f:option SegReg -> Codec X) : Codec X :=
    #x"2E" .$ f (Some CS)
||| #x"36" .$ f (Some SS)
||| #x"3E" .$ f (Some DS)
||| #x"26" .$ f (Some ES)
||| #x"64" .$ f (Some FS)
||| #x"65" .$ f (Some GS)
||| f None.
*)

Definition isHLT : CAST unit Instr.
  apply: MakeCast (fun _ => HLT)
                  (fun i => if i is HLT then Some tt else None) _.
  by case=> //.
Defined.

Definition shortQWORDEmb : CAST BYTE QWORD.
apply: MakeCast (@signExtend _ 7) (@signTruncate _ 7) _.
Proof. move => d b/= H.
admit. (* TODO: recover from bits library: by apply signTruncateK. *)
Defined.

Definition longQWORDEmb : CAST DWORD QWORD.
apply: MakeCast (@signExtend _ 31) (@signTruncate _ 31) _.
Proof. move => d b/= H. admit. (* TODO: recover from bits library: by apply signTruncateK. *)
Defined.

Definition shortDWORDCodec: Codec DWORD :=
  BYTECodec ~~> shortDWORDEmb.
Definition shortQWORDCodec: Codec QWORD :=
  BYTECodec ~~> shortQWORDEmb.
Definition longQWORDCodec: Codec QWORD :=
  DWORDCodec ~~> longQWORDEmb.

Definition ShortTgtCodec : Codec Tgt :=
  shortQWORDCodec ~~> unTgt.

Definition DWORDTgtCodec : Codec Tgt := 
  longQWORDCodec ~~> unTgt.

Definition VAXCodec s : Codec (gpVReg s) :=
match s return Codec (gpVReg s) with
| OpSize1 => always (AL:gpReg8)
| OpSize2 => always (AX:gpReg16)
| OpSize4 => always (EAX:gpReg32)
| OpSize8 => always (RAX:gpReg)
end.

Definition opcodeWithSizeCodec X (opcode:BYTE) (c : bool -> Codec X) : Codec X :=
  droplsb opcode .$ Cond c.

(*---------------------------------------------------------------------------
    TEST instruction
  ---------------------------------------------------------------------------*)
Definition tryEqOpSize F (s1 s2: opsize): F s1 -> option (F s2) :=
  match s1, s2 with
  | OpSize1, OpSize1 => fun x => Some x
  | OpSize2, OpSize2 => fun x => Some x
  | OpSize4, OpSize4 => fun x => Some x
  | OpSize8, OpSize8 => fun x => Some x
  | _, _ => fun x => None
  end. 

Definition unTEST s : CAST (regmem s * regimm s) Instr.
apply (MakeCast (fun p => TESTOP s p.1 p.2)
                (fun i => if i is TESTOP s1 x d
  then tryEqOpSize (F:= fun s=> (regmem s * regimm s)%type) s (x,d) else None)). 
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined.

Definition TESTCodec :=
  sizesPrefixCodec (fun w r =>
  rexPrefixCodec (fun W R X B =>
    (* Short form for TEST AL/AX/EAX/RAX, imm8/imm16/imm32 *)
        opcodeWithSizeCodec #x"A8" (fun d => 
        (VAXCodec (mkOpSize w W d) ~~> unRegMemR _) $ (IMMCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, imm8 | TEST r/m16, imm16 | TEST r/m32, imm32 | TEST r/m64, imm32 *)
    ||| opcodeWithSizeCodec #x"F6" (fun d =>
        RegMemOpCodec R X B #0 (mkOpSize w W d) $ (IMMCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, r8 | TEST r/m16, r16 | TEST r/m32, r32 | TEST r/m64, r64 *)
    ||| opcodeWithSizeCodec #x"84" (fun d =>
        RegMemCodec R X B (VRegCodec R _ ~~> unRegImmR _) _ ~~> swapPairCast _ _ ~~> unTEST (mkOpSize w W d))
    )).

(*---------------------------------------------------------------------------
    RET instruction (near)
  ---------------------------------------------------------------------------*)
Definition unRET : CAST WORD Instr.
apply: MakeCast RETOP (fun i => if i is RETOP w then Some w else None) _.
by elim => // ? ? [->]. 
Defined.

Definition RETCodec :=
    #x"C3" .$ always #0 ~~> unRET
||| #x"C2" .$ WORDCodec ~~> unRET.

(*---------------------------------------------------------------------------
    JMP instruction
    @TODO: 16-bit variants, far jumps
  ---------------------------------------------------------------------------*)
Definition unJMP : CAST JmpTgt Instr. 
apply: (MakeCast JMPrel (fun i => if i is JMPrel  t 
  then Some t else None) _).
by  case => //; case => // ? ? [->]. 
Defined.

(* This is an example of a codec that is mode-dependent: the DEFAULT for 64-bit mode is 64-bit,
  with or without a rex prefix *)
Definition JMPCodec :=
    #x"EB" .$ ShortTgtCodec ~~> unJmpTgtI ~~> unJMP 
||| #x"E9" .$ DWORDTgtCodec ~~> unJmpTgtI ~~> unJMP 
||| rexPrefixCodec (fun W R X B =>
    #x"FF" .$ RegMemOpCodec R X B #4 OpSize8 ~~> unJmpTgtRM ~~> unJMP).

(*---------------------------------------------------------------------------
    CALL instruction
    @TODO: 16-bit variants, far calls
  ---------------------------------------------------------------------------*)
Definition unCALL : CAST JmpTgt Instr.
apply: MakeCast CALLrel (fun i => if i is CALLrel t 
  then Some t else None) _.
by  case => //; case => // ? ? [->]. 
Defined.

Definition CALLCodec :=
    #x"E8" .$ DWORDTgtCodec ~~> unJmpTgtI ~~> unCALL
||| rexPrefixCodec (fun W R X B =>
    #x"FF" .$ RegMemOpCodec R X B #2 OpSize8 ~~> unJmpTgtRM ~~> unCALL).


(*---------------------------------------------------------------------------
    JCC instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unJCC : CAST (Condition*bool*Tgt) Instr.
apply: (MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _).
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.

Definition JCCCodec :=
    #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ DWORDTgtCodec ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec ~~> unJCC.

(*---------------------------------------------------------------------------
    SET instruction
  ---------------------------------------------------------------------------*)
Definition unSET : CAST (Condition*bool*gpVReg OpSize1) Instr.
apply: (MakeCast (fun p => let: (c,d,t) := p in SET c (negb d) t)
                 (fun i => if i is SET c d t then Some(c,negb d,t) else None) _).
Proof.
  elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
    by rewrite negbK.
Defined.

Definition SETCodec :=
  rexPrefixCodec (fun W R X B =>
  #x"0F" .$ SET32PREF .$ conditionCodec $ Any $ VRegCodec R _) ~~> unSET.


(*---------------------------------------------------------------------------
    PUSH instruction
  ---------------------------------------------------------------------------*)
Definition unPUSH : CAST src Instr.
apply (MakeCast PUSH
                (fun i => if i is PUSH x then Some x else None)).
by case=> //; congruence.
Defined. 

(* TODO: FIX
Definition PUSHCodec := 
  (sizesPrefixCodec (fun w r =>
   rexPrefixCodec (fun W R X B =>
       (#x"68" .$ IMMCodec _ ~~> unSrcI _
(*    ||| #x"6A" .$ shortDWORDCodec ~~> unSrcI _ *)
    ||| #b"01010" .$ VRegCodec R _ ~~> unSrcR _) ~~> unPUSH (mkOpSize w W false))))
(*||| segPrefixCodec (fun seg =>
    #x"FF" .$ RegMemOpCodec seg AdSize4 false false false #6 _ ~~> unSrcRM ~~> unPUSH)*)
.
*)

(*---------------------------------------------------------------------------
    POP instruction
  ---------------------------------------------------------------------------*)
Definition unPOP s : CAST (regmem s) Instr.
apply (MakeCast (@POP s) 
                (fun i => if i is POP s' x then tryEqOpSize (F:=regmem) s x else None)).
case: s; do 2 case=> //=; congruence.
Defined. 

Definition POPCodec :=
  (sizesPrefixCodec (fun w r =>
   rexPrefixCodec (fun W R X B =>
   #x"8F" .$ RegMemOpCodec R X B #0 _ ~~> unPOP (mkOpSize w W false))))
(* @TODO: 16-bit and 32-bit register versions *)
||| #b"01011" .$ GPReg64Codec false ~~> unRegMemR OpSize8 ~~> unPOP OpSize8.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)

Definition unMOV w W d : CAST (dstsrc (mkOpSize w W d)) Instr.
apply (MakeCast (MOVOP _) (fun i => if i is MOVOP _ d then tryEqOpSize _ d else None)). 
by elim:w; elim:d; elim:W; elim => //; elim => //; move => ? src [->]. 
Defined. 

Definition MOVCodec :=  
  sizesPrefixCodec (fun w r =>
  rexPrefixCodec (fun W R X B =>
      (* MOV r/m8, r8 | MOV r/m16, r16 | MOV r/m32, r32 *)
      opcodeWithSizeCodec #x"88" (fun d =>
        RegMemCodec R X B (VRegCodec R _) _ ~~> unDstSrcMRR _ ~~> unMOV w W d)
      (* MOV r8, r/m8 | MOV r16, r/m16 | MOV r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"8A" (fun d =>   
        RegMemCodec R X B (VRegCodec R _) _  ~~> unDstSrcRMR _ ~~> unMOV w W d))).
(*
      (* MOV r/m8, imm8 | MOV r/m16, imm16 | MOV r/m32, imm32 *)
  ||| opcodeWithSizeCodec #x"C6" (fun d =>
        RegMemOpCodec a R X B #0 _ $ IMMCodec _ ~~> unMovDstSrcMRI _ ~~> unMOV w d)
*)

  (*
      (* TODO: get this right. It takes a full 64-bit immediate! *)
      (* MOV r8, imm8 | MOV r16, imm16 | MOV r32, imm32 | MOV r64, imm64 *)
  ||| #x"B" .$ Cond (fun d => 
        VRegCodec R _ $ VWORDCodec _ ~~> unDstSrcRI _ ~~> unMOV w W d))) *)

                  
(*---------------------------------------------------------------------------
    MOVX instruction
  ---------------------------------------------------------------------------*)

Definition unMOVZX : CAST (gpReg32 * regmem OpSize1) Instr.
  refine (MakeCast (fun v => MOVX false v.1 v.2) 
                   (fun i => if i is MOVX false v1 v2
                             then Some (v1, v2)
                             else None) _).
  case=> x //=;
  case: x => dst src [_ _] //= [<- <-] //.
Defined.


Definition MOVZXCodec :=
  sizesPrefixCodec (fun w r =>
  rexPrefixCodec (fun W R X B =>
  #x"0FB6" .$  RegMemCodec R X B (VRegCodec R OpSize4) OpSize1 ~~> unMOVZX)).

(*---------------------------------------------------------------------------
    BT, BTC, BTR, BTS instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unBITOPR : CAST (BitOp * (gpReg32 * regmem OpSize4)) Instr.
apply: (MakeCast (fun p => let: (op,(r,rm)) := p in BITOP op rm (inl r))
                (fun i => if i is BITOP op y (inl r) then Some(op,(r,y)) else None) _).
elim => //. move => op dst src [op' [dst' src']]. case src => // r. by move => [-> -> ->].
Defined.

Definition unBITOPI : CAST (BitOp * regmem OpSize4 * BYTE) Instr.
apply: (MakeCast (fun p => let: (op,rm,b) := p in BITOP op rm (inr b))
                (fun i => if i is BITOP op y (inr b) then Some(op,y,b) else None) _).
elim => //. move => op dst src [[op' dst'] src']. case src => // r. by move => [-> -> ->].
Defined.

Definition BITCodec :=
    #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec false false false (GPReg32Codec false) _) ~~> unBITOPR
||| #x"0F" .$ #x"BA" .$ RegMemCodec false false false (#b"1" .$ bitOpCodec) _ $ BYTECodec ~~> unBITOPI.


(*---------------------------------------------------------------------------
    SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unShiftCountCL : CAST unit ShiftCount.
apply: MakeCast (fun _=>ShiftCountCL) (fun c => if c is ShiftCountCL then Some tt else None) _.
elim; congruence.
Defined.

Definition unShiftCountI : CAST BYTE ShiftCount.
apply: MakeCast ShiftCountI (fun c => if c is ShiftCountI b then Some b else None) _.
elim; congruence.
Defined.

Definition unSHIFT s : CAST (ShiftOp * regmem s * ShiftCount) Instr.
eapply (MakeCast (fun p => let: (op,v,count) := p in SHIFTOP _ op v count)
                 (fun i => if i is SHIFTOP s1 op v count 
  then tryEqOpSize (F:= fun s=> (ShiftOp*regmem s*ShiftCount)%type) s (op,v,count) else None)).
elim:s; elim => //; elim => //; move => ? ? src [[? ?] ?]; by move => [-> -> ->]. 
Defined.

Definition SHIFTCodec :=  
  sizesPrefixCodec (fun w r => 
    (
      opcodeWithSizeCodec #x"C0" (fun d => 
        RegMemCodec false false false shiftOpCodec (mkOpSize w false d) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D0" (fun d =>
        RegMemCodec false false false shiftOpCodec (mkOpSize w false d) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D2" (fun d =>
        RegMemCodec false false false shiftOpCodec (mkOpSize w false d) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT _)
    )
  ).

(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
Definition unBOP s : CAST (BinOp * dstsrc s) Instr.
apply: (MakeCast (fun p => BOP _ p.1 p.2))
                 (fun i => if i is BOP s1 op v 
                  then tryEqOpSize (F:=fun s => (BinOp*dstsrc s)%type) s (op,v) else None) _.  elim:s; elim => //; elim => //; move => ? src [? ?]; by move => [-> ->]. 
Defined.

Definition shortVWORDEmb w : CAST BYTE (VWORD (if w then OpSize2 else OpSize4)).
destruct w. 
apply: MakeCast (@signExtend 8 7) (@signTruncate 8 7) _.
- move => d b/= H. admit. (* TODO: import results  by apply signTruncateK. *)
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
- move => d b/= H. admit. (* TODO: by apply signTruncateK. *)
Defined.

Definition shortVWORDCodec w: Codec _ :=
  BYTECodec ~~> shortVWORDEmb w.

Definition BINOPCodec :=
    sizesPrefixCodec (fun w r => 
    rexPrefixCodec (fun W R X B =>
      (* OP AL, imm8 | OP AX, imm16 | OP EAX, imm32 | OP RAX, imm32 *)
    #b"00" .$ opCodec $ #b"100" .$ 
      (VAXCodec _ $ IMMCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"101" .$ 
      (VAXCodec _ $ IMMCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w W true)

    (* OP r/m8, r8 | OP r/m16, r16 | OP r/m32, r32 | OP r/m64, r64 *)
||| #b"00" .$ opCodec $ #b"010" .$ 
      (RegMemCodec R X B (VRegCodec R _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"011" .$ 
      (RegMemCodec R X B (VRegCodec R _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w W true)

    (* OP r8, r/m8 | OP r16, r/m16 | OP r32, r/m32 | OP r64, r/m64 *)
||| #b"00" .$ opCodec $ #b"000" .$ 
      (RegMemCodec R X B (VRegCodec R _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"001" .$ 
      (RegMemCodec R X B (VRegCodec R _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w W true)

    (* OP r/m8, imm8 | OP r/m16, imm16 | OP r/m32, imm32 | OP r/m64, imm32 *)
||| opcodeWithSizeCodec #x"80" (fun d => RegMemCodec R X B opCodec _ $ IMMCodec _
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP (mkOpSize w W d))

(*
    (* OP r/m16, imm8 | OP r/m32, imm8 (sign-extended) *)
||| #x"83" .$ (RegMemCodec opCodec _ $ shortVWORDCodec w) 
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP _ 
*)
    ))
.

(*---------------------------------------------------------------------------
    INC/DEC/NOT/NEG instructions
  ---------------------------------------------------------------------------*)
Definition unINC s : CAST (regmem s) Instr.
apply: MakeCast (fun v => UOP _ OP_INC v)
                (fun i => if i is UOP s1 OP_INC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unDEC s : CAST (regmem s) Instr.
apply: MakeCast (fun v => UOP _ OP_DEC v)
                (fun i => if i is UOP s1 OP_DEC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNEG s : CAST (regmem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NEG v)
                (fun i => if i is UOP s1 OP_NEG v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNOT s : CAST (regmem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NOT v)
                (fun i => if i is UOP s1 OP_NOT v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition UOPCodec :=
  sizesPrefixCodec (fun w r => 
  rexPrefixCodec (fun W R X B =>
    opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec R X B #0 _ ~~> unINC (mkOpSize w false d))

||| opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec R X B #1 _ ~~> unDEC (mkOpSize w false d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec R X B #2 _ ~~> unNOT (mkOpSize w false d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec R X B #3 _ ~~> unNEG (mkOpSize w false d))

(* @TODO: make these available only in 32-bit mode; in 64-bit mode these are REX prefixes *)
(*
||| INCPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unINC (mkOpSize w false false)
||| DECPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unDEC (mkOpSize w false false)
*)
  )).


(*---------------------------------------------------------------------------
    MUL and IMUL instructions
  ---------------------------------------------------------------------------*)

(*
Definition unImulDstSrcRM s : CAST (regmem s) (imuldstsrc s).
apply: (MakeCast
       (fun p => match p with RegMemR y => (ImulDstSrcR s y)
                            | RegMemM a y => (ImulDstSrcM s a y) end)
       (fun ds => match ds with ImulDstSrcR x => Some (RegMemR _ x)
                              | ImulDstSrcM a x => Some (RegMemM _ a x)
                              | _ => None end) _).
case=> x //. 
- by case=> y // [<-].
- by move=> src ? [<-].
Defined.
*)
Definition unImulDstSrcRRM s : CAST (gpVReg s * regmem s) (imuldstsrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => (ImulDstSrcRR s p.1 y)
                              | RegMemM y => (ImulDstSrcRM s p.1 y) end)
       (fun ds => match ds with ImulDstSrcRR x y => Some (x, RegMemR _ y)
                              | ImulDstSrcRM x y => Some (x, RegMemM _ y)
                              | _ => None end) _).
case=> x //.
- by move=> src [? ?] [<-] [<-].
- by move=> src [? ?] [<-] [<-].
Defined.

Definition unImulDstSrcRRMI s : CAST (gpVReg s * regmem s * IMM s) (imuldstsrc s).
apply: (MakeCast
       (fun p => match p.1.2 with RegMemR y => (ImulDstSrcRRI s p.1.1 y p.2)
                                | RegMemM y => (ImulDstSrcRMI s p.1.1 y p.2) end)
       (fun ds => match ds with ImulDstSrcRRI x y i => Some (x, RegMemR _ y, i)
                              | ImulDstSrcRMI x y i => Some (x, RegMemM _ y, i)
                              | _ => None end) _).
case=> x //.
- by move=> src c [? ?] [<-] [<-].
- by move=>  src c [? ?] [<-] [<-].
Defined.

Definition unIMUL w W d : CAST (imuldstsrc (mkOpSize w W d)) Instr.
  apply: (MakeCast (fun p => IMUL _ p) 
                   (fun i => if i is IMUL _ p then
                               tryEqOpSize (mkOpSize w W d) p
                             else None) _).
  case: w; case: W; case: d; case=> //; case=> //= ? ? [<-] //=.
Defined.

Definition unMUL s : CAST (regmem s) Instr.
apply: (MakeCast (@MUL s)
                 (fun i => if i is MUL s1 v 
                  then tryEqOpSize s v else None) _).  
case: s; case=> //; case=> //= q ? [<-] //.
Defined.

Definition MULCodec :=
  sizesPrefixCodec (fun w r => 
  rexPrefixCodec (fun W R X B =>
  (*  IMUL r16, r/m16 | IMUL r32, r/m32 | IMUL r64, r/m64 *)
  (#x"0FAF" .$ (RegMemCodec R X B (VRegCodec R _) _ ~~>  unImulDstSrcRRM _)
   ~~> unIMUL w W false)
  (* IMUL r16, r/m16, imm16 | IMUL r32, r/m32, imm32 | IMUL r64, r/m64, imm32 *)
||| #x"69" .$ 
     (RegMemCodec R X B (VRegCodec R _) _ $
      IMMCodec _ ~~>  unImulDstSrcRRMI _) ~~> (unIMUL  w W false))
  (* MUL r/m8 | MUL r/m16 | MUL r/m32 *)
||| opcodeWithSizeCodec #x"F6" (fun d =>  
    RegMemOpCodec false false false #4 _ ~~> unMUL (mkOpSize w false d))).


(*---------------------------------------------------------------------------
    LEA instruction 
  ---------------------------------------------------------------------------*)
Definition unLEA s : CAST (gpVReg s * regmem s) Instr.
  apply: (MakeCast (fun p => LEA s p.1 p.2) 
                   (fun i => if i is LEA s' x  y then 
                               tryEqOpSize (F:= fun s=> (gpVReg s * regmem s)%type) s (x,y)
                             else None) _).
by elim: s; elim => //; elim => //; move => r q [a b] [-> <-]. Defined.

Definition LEACodec :=
  sizesPrefixCodec (fun w r =>     
  rexPrefixCodec (fun W R X B =>
  #x"8D" .$ RegMemCodec R X B (VRegCodec R _) _ ~~> unLEA (mkOpSize w W true))).

(*---------------------------------------------------------------------------
    XCHG instruction 
  ---------------------------------------------------------------------------*)
Definition unXCHG s : CAST (gpVReg s * regmem s) Instr. 
  apply: MakeCast (fun p => XCHG s p.1 p.2) 
  (fun i => if i is XCHG s1 x y 
            then tryEqOpSize (F:=fun s => (gpVReg s * regmem s)%type) s (x,y) else None) _.  
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; try move => [-> ->] //=; move=> ? [-> ->] //=.
Defined. 

(*
Definition XCHGCodec :=
    opSizePrefixCodec (fun w => 
      (* XCHG AX, r16 | XCHG EAX, r32 *)
      #b"10010" .$ VAXCodec _ $ (VRegCodec false _ ~~> unRegMemR _) ~~> unXCHG (mkOpSize w false true)
      (* XCHG r8, r/m8 | XCHG r16, r/m16 | XCHG r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"86" (fun d =>
        RegMemCodec None _ false _ _ (VRegCodec false _) ~~> unXCHG (mkOpSize w false d))
  ).
 *)

(*---------------------------------------------------------------------------
    CQO instruction 
  ---------------------------------------------------------------------------*)

Definition unCQO : CAST unit Instr.
  refine (MakeCast (fun _ => CQO)
                   (fun i => if i is CQO then Some tt else None)
                   _).
  case=> x //=.
Defined.
  
Definition CQOCodec :=
  rexPrefixCodec (fun W R X B =>
                    if W then #x"99" ~~> unCQO 
                    else Void Instr).

(*---------------------------------------------------------------------------
    MOVABS instruction 
  ---------------------------------------------------------------------------*)


Definition unMOVABS : CAST (gpReg * QWORD) Instr.
  refine (MakeCast (fun (p: gpReg * QWORD) => let (r, i) := p in MOVABS r i)
                   (fun i => if i is MOVABS r i
                             then Some (r, i)
                             else None) _).
  case=> x //= y [_ _] [<- <-] //=.
Defined.

Definition MOVABSCodec :=  
  rexPrefixCodec (fun W R X B =>
                    #x"B8" .$ 
                     VRegCodec R OpSize8 $
                     VWORDCodec OpSize8 ~~> unMOVABS).


(*---------------------------------------------------------------------------
    MOVQ instruction 
  ---------------------------------------------------------------------------*)

(*
Definition unXMemR : CAST XMMreg XMem.
apply: MakeCast XMemR (fun rm => if rm is XMemR r then Some r else None) _.
by elim; congruence. Defined.
*)
Definition XMMregCodec (vexBit:bool) : Codec XMMreg :=
if vexBit then 
    #b"000" .$ always (XMM8:XMMreg)
||| #b"001" .$ always (XMM9:XMMreg)
||| #b"010" .$ always (XMM10:XMMreg)
||| #b"011" .$ always (XMM11:XMMreg)
||| #b"100" .$ always (XMM12:XMMreg)
||| #b"101" .$ always (XMM13:XMMreg)
||| #b"110" .$ always (XMM14:XMMreg)
||| #b"111" .$ always (XMM15:XMMreg)
else
    #b"000" .$ always (XMM0:XMMreg)
||| #b"001" .$ always (XMM1:XMMreg)
||| #b"010" .$ always (XMM2:XMMreg)
||| #b"011" .$ always (XMM3:XMMreg)
||| #b"100" .$ always XMM4
||| #b"110" .$ always (XMM5:XMMreg)
||| #b"111" .$ always (XMM6:XMMreg)
||| #b"101" .$ always (XMM7:XMMreg).


(* TODO: is that encoding correct? unlikely. *)
Definition unXMem : CAST (regmem OpSize8) XMem. 
refine (MakeCast
          (fun p: regmem OpSize8  => match p with
                      | RegMemM m => XMemM m
                      | RegMemR (mkGPReg RAX) => XMemR XMM0
                      | RegMemR (mkGPReg RBX) => XMemR XMM1
                      | RegMemR (mkGPReg RCX) => XMemR XMM2
                      | RegMemR (mkGPReg RDX) => XMemR XMM3
                      | RegMemR (mkGPReg RSI) => XMemR XMM4
                      | RegMemR (mkGPReg RDI) => XMemR XMM5
                      | RegMemR RSP => XMemR XMM6
                      | RegMemR (mkGPReg RBP) => XMemR XMM7
                      | RegMemR (mkGPReg R8) => XMemR XMM8
                      | RegMemR (mkGPReg R9) => XMemR XMM9
                      | RegMemR (mkGPReg R10) => XMemR XMM10
                      | RegMemR (mkGPReg R11) => XMemR XMM11
                      | RegMemR (mkGPReg R12) => XMemR XMM12
                      | RegMemR (mkGPReg R13) => XMemR XMM13
                      | RegMemR (mkGPReg R14) => XMemR XMM14
                      | RegMemR (mkGPReg R15) => XMemR XMM15 end)
          (fun p => match p with
                      | XMemM m => Some (RegMemM _ m)
                      | XMemR XMM0 => Some (RegMemR OpSize8 (mkGPReg RAX)) 
                      | XMemR XMM1 => Some (RegMemR OpSize8 (mkGPReg RBX)) 
                      | XMemR XMM2 => Some (RegMemR OpSize8 (mkGPReg RCX)) 
                      | XMemR XMM3 => Some (RegMemR OpSize8 (mkGPReg RDX)) 
                      | XMemR XMM4 => Some (RegMemR OpSize8 (mkGPReg RSI)) 
                      | XMemR XMM5 => Some (RegMemR OpSize8 (mkGPReg RDI)) 
                      | XMemR XMM6 => Some (RegMemR OpSize8 RSP) 
                      | XMemR XMM7 => Some (RegMemR OpSize8 (mkGPReg RBP)) 
                      | XMemR XMM8 => Some (RegMemR OpSize8 (mkGPReg R8)) 
                      | XMemR XMM9 => Some (RegMemR OpSize8 (mkGPReg R9)) 
                      | XMemR XMM10 => Some (RegMemR OpSize8 (mkGPReg R10)) 
                      | XMemR XMM11 => Some (RegMemR OpSize8 (mkGPReg R11)) 
                      | XMemR XMM12 => Some (RegMemR OpSize8 (mkGPReg R12)) 
                      | XMemR XMM13 => Some (RegMemR OpSize8 (mkGPReg R13)) 
                      | XMemR XMM14 => Some (RegMemR OpSize8 (mkGPReg R14)) 
                      | XMemR XMM15 => Some (RegMemR OpSize8 (mkGPReg R15)) 
                    end) _).
case=> //. 
- by case=> //; case=> // ? [<-].
- by move=> ? ? [<-].
Defined.

Definition unXmmdstsrcXRM : CAST (XMMreg * XMem) xmmdstsrc.
apply: (MakeCast
       (fun p => XMMDstSrcXRM p.1 p.2)
       (fun ds => if ds is XMMDstSrcXRM dst src then Some (dst, src) else None) _).
by case=> reg // src [? ?] [<- <-].
Defined.

Definition unXmmdstsrcRMX : CAST (XMMreg * XMem) xmmdstsrc.
apply: (MakeCast
       (fun p => XMMDstSrcRMX p.2 p.1)
       (fun ds => if ds is XMMDstSrcRMX dst src then Some (src, dst) else None) _).
by case=> reg // src [? ?] [<- <-].
Defined.

Definition unMOVQ : CAST xmmdstsrc Instr.
refine (MakeCast (fun r => MOVQ r)
                 (fun i => if i is MOVQ r then Some r else None)
                 _).
case=> //; move=> x _ [<-] //.
Defined.

Definition MOVQCodec :=
  sizesPrefixCodec (fun w r =>
  rexPrefixCodec (fun W R X B =>
  (* MOVQ xmm1, xmm2/m64
     Prefix: F3 
     TODO: is that enforced? *)
  #x"0F7E" .$ 
   RegMemCodec R X B (XMMregCodec R) _ ~~> 
   pairOfCasts (idCast _) unXMem ~~>
   unXmmdstsrcXRM ~~> 
   unMOVQ
||| (* MOVQ xmm2/m64, xmm1 
    Prefix: 66, TODO: is that enforced ? *)
  #x"0FD6" .$ 
   RegMemCodec R X B (XMMregCodec R) _ ~~> 
   pairOfCasts (idCast _) unXMem ~~>
   unXmmdstsrcRMX ~~> 
   unMOVQ)).

(*---------------------------------------------------------------------------
    All instructions
  ---------------------------------------------------------------------------*)
Definition InstrCodec : Codec (Instr) :=
(* Nullary operations *)
    #x"F4" ~~> isHLT
(* Everything else *)
||| JMPCodec ||| CALLCodec ||| TESTCodec ||| (* TODO: restore PUSHCodec ||| *) POPCodec ||| RETCodec
||| MOVCodec ||| BITCodec ||| SHIFTCodec ||| JCCCodec ||| BINOPCodec ||| UOPCodec
||| LEACodec ||| (* XCHGCodec ||| *) MULCodec ||| SETCodec ||| CQOCodec
||| MOVABSCodec ||| MOVZXCodec ||| MOVQCodec.

(*
Definition MaxBits := Eval vm_compute in Option.default 0 (maxSize InstrCodec).

Require Import common.monad x86proved.reader x86proved.bitreader.
Instance readOptionInstr : Reader (option Instr) :=
  let! (resbits, i) = bitReaderToReader (codecToBitReader MaxBits InstrCodec) nil;
  retn i.

Instance readInstr : Reader Instr :=
  let! pc = readCursor;
  if pc is mkCursor p
  then
    let! r = readOptionInstr;
    if r is Some i then retn i else retn BADINSTR
  else
    retn BADINSTR.



*)