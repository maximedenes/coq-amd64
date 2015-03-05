(*======================================================================================
  Instruction codec
  ======================================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.seq Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.fintype.
Require Import x86proved.bits Ssreflect.eqtype Ssreflect.tuple.
Require Import Coq.Strings.String.
Require Import codec.cast codec.codec codec.bitscodec.
Require Import x86proved.x86.instr x86proved.x86.encdechelp x86proved.x86.addr x86proved.x86.reg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Casts for datatypes used in instructions
  ---------------------------------------------------------------------------*)
Definition unSrcR s : CAST (GPReg s) (Src s).
apply: MakeCast (SrcR _) (fun src => if src is SrcR r then Some r else None) _.
by elim; congruence. Defined.

Definition unSrcI s : CAST (IMM s) (Src s).
apply: MakeCast (SrcI _) (fun s => if s is SrcI i then Some i else None) _.
by elim; congruence. Defined.

Definition unRegMemR d : CAST (GPReg d) (RegMem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmR d : CAST (GPReg d) (RegImm d).
apply: MakeCast (RegImmR d) (fun rm => if rm is RegImmR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmI d : CAST (IMM d) (RegImm d).
apply: MakeCast (RegImmI d) (fun rm => if rm is RegImmI v then Some v else None) _.
by elim; congruence. Defined.

Definition unJmpTgtI a : CAST (Tgt a) (JmpTgt a).
apply: (MakeCast (JmpTgtI a) (fun t => if t is JmpTgtI d then Some d else None) _).
elim; elim; congruence. Defined.

Definition unJmpTgtRM a : CAST (RegMem (adSizeToOpSize a)) (JmpTgt a).
apply: (MakeCast (JmpTgtRegMem _)
  (fun i => if i is JmpTgtRegMem rm then Some rm else None) _).
by elim; congruence. Defined.

Definition unTgt a : CAST (VWORD (adSizeToOpSize a)) (Tgt a).
apply: (MakeCast (mkTgt a) (fun t => let: mkTgt d := t in Some d) _).
by move => [d] y [<-].
Defined.

Definition unSrcRM s : CAST (RegMem s) (Src s).
apply: (MakeCast
  (fun (rm: RegMem s) => match rm with RegMemR r => SrcR _ r | RegMemM a m => SrcM _ a m end)
  (fun i => match i with SrcR r => Some (RegMemR s r) | SrcM _ m => Some (RegMemM _ _ m)
                       | _ => None
            end) _).
elim => //. 
- by move => a ms y [<-]. 
- by move => ? ? [<-]. Defined.

(*---------------------------------------------------------------------------
    Casts and codecs for bit-encoded types e.g. registers, scales, conditions
  ---------------------------------------------------------------------------*)

(* 32-bit register encoding, including ESP *)
Definition GPReg32Codec (rexBit:bool) : Codec GPReg32 :=
if rexBit then
    #b"000" .$ always (R8D:GPReg32)
||| #b"001" .$ always (R9D:GPReg32)
||| #b"010" .$ always (R10D:GPReg32)
||| #b"011" .$ always (R11D:GPReg32)
||| #b"100" .$ always (R12D:GPReg32)
||| #b"101" .$ always (R13D:GPReg32)
||| #b"110" .$ always (R14D:GPReg32)
||| #b"111" .$ always (R15D:GPReg32)
else
    #b"000" .$ always (EAX:GPReg32)
||| #b"001" .$ always (ECX:GPReg32)
||| #b"010" .$ always (EDX:GPReg32)
||| #b"011" .$ always (EBX:GPReg32)
||| #b"100" .$ always ESP
||| #b"110" .$ always (ESI:GPReg32)
||| #b"111" .$ always (EDI:GPReg32)
||| #b"101" .$ always (EBP:GPReg32).

(* 64-bit register encoding, including RSP *)
Definition GPReg64Codec (rexBit:bool) : Codec GPReg64 :=
if rexBit then 
    #b"000" .$ always (R8:GPReg64)
||| #b"001" .$ always (R9:GPReg64)
||| #b"010" .$ always (R10:GPReg64)
||| #b"011" .$ always (R11:GPReg64)
||| #b"100" .$ always (R12:GPReg64)
||| #b"101" .$ always (R13:GPReg64)
||| #b"110" .$ always (R14:GPReg64)
||| #b"111" .$ always (R15:GPReg64)
else
    #b"000" .$ always (RAX:GPReg64)
||| #b"001" .$ always (RCX:GPReg64)
||| #b"010" .$ always (RDX:GPReg64)
||| #b"011" .$ always (RBX:GPReg64)
||| #b"100" .$ always RSP
||| #b"110" .$ always (RSI:GPReg64)
||| #b"111" .$ always (RDI:GPReg64)
||| #b"101" .$ always (RBP:GPReg64).
  
(* Non-SP, 16-bit register encoding *)
Definition NonSPReg16Codec (rexBit:bool) : Codec NonSPReg16 :=
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
Definition SIBIxReg32Codec X : Codec (option (IxReg AdSize4)) :=
if X
then
    #b"000" .$ always (Some R8D)
||| #b"001" .$ always (Some R9D)
||| #b"010" .$ always (Some R10D)
||| #b"011" .$ always (Some R11D)
||| #b"100" .$ always (Some R12D)
||| #b"101" .$ always (Some R13D)
||| #b"110" .$ always (Some R14D)
||| #b"111" .$ always (Some R15D)
else
    #b"000" .$ always (Some EAX)
||| #b"001" .$ always (Some ECX)
||| #b"010" .$ always (Some EDX)
||| #b"011" .$ always (Some EBX)
||| #b"100" .$ always None
||| #b"110" .$ always (Some ESI)
||| #b"111" .$ always (Some EDI)
||| #b"101" .$ always (Some EBP).
  
Definition SIBIxReg64Codec X : Codec (option (IxReg AdSize8)) :=
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

Definition SIBIxRegCodec a X : Codec (option (IxReg a)) :=
  match a return Codec (option (IxReg a)) with
  | AdSize4 => SIBIxReg32Codec X
  | AdSize8 => SIBIxReg64Codec X
  end.

(* This isn't quite right as EBP can't be used as a base with mod 00 - see table 2-3 *)
Definition SIBBaseRegCodec a X : Codec (BaseReg a) :=
  match a return Codec (BaseReg a) with
  | AdSize4 => GPReg32Codec X
  | AdSize8 => GPReg64Codec X
  end.


(* Can't encode R12 or R13 this way - see Table 2-5 *)
Definition NonBPNonSPBaseReg32Codec B : Codec (BaseReg AdSize4) :=
if B then
    #b"000" .$ always (R8D: BaseReg AdSize4)
||| #b"001" .$ always (R9D: BaseReg AdSize4)
||| #b"010" .$ always (R10D: BaseReg AdSize4)
||| #b"011" .$ always (R11D: BaseReg AdSize4)
||| #b"110" .$ always (R14D: BaseReg AdSize4)
||| #b"111" .$ always (R15D: BaseReg AdSize4)
else
    #b"000" .$ always (EAX: BaseReg AdSize4)
||| #b"001" .$ always (ECX: BaseReg AdSize4)
||| #b"010" .$ always (EDX: BaseReg AdSize4)
||| #b"011" .$ always (EBX: BaseReg AdSize4)
||| #b"110" .$ always (ESI: BaseReg AdSize4)
||| #b"111" .$ always (EDI: BaseReg AdSize4)
.

Definition NonBPBaseReg32Codec B : Codec (BaseReg AdSize4) :=
  NonBPNonSPBaseReg32Codec B
||| #b"100" .$ always ESP.


Definition NonBPNonSPBaseReg64Codec B : Codec (BaseReg AdSize8) :=
if B then
    #b"000" .$ always (R8: BaseReg _)
||| #b"001" .$ always (R9: BaseReg _)
||| #b"010" .$ always (R10: BaseReg _)
||| #b"011" .$ always (R11: BaseReg _)
||| #b"110" .$ always (R14: BaseReg _)
||| #b"111" .$ always (R15: BaseReg _)
else
    #b"000" .$ always (RAX: BaseReg _)
||| #b"001" .$ always (RCX: BaseReg _)
||| #b"010" .$ always (RDX: BaseReg _)
||| #b"011" .$ always (RBX: BaseReg _)
||| #b"110" .$ always (RSI: BaseReg _)
||| #b"111" .$ always (RDI: BaseReg _)
.

Definition NonBPBaseReg64Codec B : Codec (BaseReg AdSize8) :=
  NonBPNonSPBaseReg64Codec B
||| #b"100" .$ always RSP.

Definition NonBPNonSPBaseRegCodec a B : Codec (BaseReg a) :=
  match a return Codec (BaseReg a) with
  | AdSize4 => NonBPNonSPBaseReg32Codec B
  | AdSize8 => NonBPNonSPBaseReg64Codec B
  end.

Definition NonBPBaseRegCodec a B : Codec (BaseReg a) :=
  match a return Codec (BaseReg a) with
  | AdSize4 => NonBPBaseReg32Codec B
  | AdSize8 => NonBPBaseReg64Codec B
  end.

Definition NonSPBaseReg32Codec B : Codec (BaseReg AdSize4) :=
if B then
    #b"000" .$ always (R8D: BaseReg AdSize4)
||| #b"001" .$ always (R9D: BaseReg AdSize4)
||| #b"010" .$ always (R10D: BaseReg AdSize4)
||| #b"011" .$ always (R11D: BaseReg AdSize4)
||| #b"101" .$ always (R13D: BaseReg AdSize4)
||| #b"110" .$ always (R14D: BaseReg AdSize4)
||| #b"111" .$ always (R15D: BaseReg AdSize4)
else
    #b"000" .$ always (EAX: BaseReg AdSize4)
||| #b"001" .$ always (ECX: BaseReg AdSize4)
||| #b"010" .$ always (EDX: BaseReg AdSize4)
||| #b"011" .$ always (EBX: BaseReg AdSize4)
||| #b"101" .$ always (EBP: BaseReg AdSize4)
||| #b"110" .$ always (ESI: BaseReg AdSize4)
||| #b"111" .$ always (EDI: BaseReg AdSize4)
.

Definition NonSPBaseReg64Codec B : Codec (BaseReg AdSize8) :=
if B then
    #b"000" .$ always (R8: BaseReg _)
||| #b"001" .$ always (R9: BaseReg _)
||| #b"010" .$ always (R10: BaseReg _)
||| #b"011" .$ always (R11: BaseReg _)
||| #b"101" .$ always (R13: BaseReg _)
||| #b"110" .$ always (R14: BaseReg _)
||| #b"111" .$ always (R15: BaseReg _)
else
    #b"000" .$ always (RAX: BaseReg _)
||| #b"001" .$ always (RCX: BaseReg _)
||| #b"010" .$ always (RDX: BaseReg _)
||| #b"011" .$ always (RBX: BaseReg _)
||| #b"101" .$ always (RBP: BaseReg _)
||| #b"110" .$ always (RSI: BaseReg _)
||| #b"111" .$ always (RDI: BaseReg _)
.

Definition NonSPBaseRegCodec a B : Codec (BaseReg a) :=
  match a return Codec (BaseReg a) with
  | AdSize4 => NonSPBaseReg32Codec B
  | AdSize8 => NonSPBaseReg64Codec B
  end.

Definition sreg3Codec : Codec SegReg :=
    #b"000" .$ always ES
||| #b"001" .$ always CS
||| #b"010" .$ always SS
||| #b"011" .$ always DS
||| #b"100" .$ always FS
||| #b"101" .$ always GS.


Definition Reg8Codec (rexBit:bool): Codec Reg8 := 
if rexBit then
    #b"000" .$ always (R8L:Reg8)
||| #b"001" .$ always (R9L:Reg8)
||| #b"010" .$ always (R10L:Reg8)
||| #b"011" .$ always (R11L:Reg8)
||| #b"100" .$ always (R12L:Reg8)
||| #b"101" .$ always (R13L:Reg8)
||| #b"110" .$ always (R14L:Reg8)
||| #b"111" .$ always (R15L:Reg8)
else
    #b"000" .$ always (AL:Reg8)
||| #b"001" .$ always (CL:Reg8)
||| #b"010" .$ always (DL:Reg8)
||| #b"011" .$ always (BL:Reg8)
||| #b"100" .$ always AH
||| #b"101" .$ always CH
||| #b"110" .$ always DH
||| #b"111" .$ always BH.

Definition GPReg16Codec (rexBit:bool) : Codec GPReg16 := 
if rexBit then
    #b"000" .$ always (R8W:GPReg16)
||| #b"001" .$ always (R9W:GPReg16)
||| #b"010" .$ always (R10W:GPReg16)
||| #b"011" .$ always (R11W:GPReg16)
||| #b"100" .$ always (R12W:GPReg16)
||| #b"101" .$ always (R13W:GPReg16)
||| #b"110" .$ always (R14W:GPReg16)
||| #b"111" .$ always (R15W:GPReg16)
else
    #b"000" .$ always (AX:GPReg16)
||| #b"001" .$ always (CX:GPReg16)
||| #b"010" .$ always (DX:GPReg16)
||| #b"011" .$ always (BX:GPReg16)
||| #b"100" .$ always SP
||| #b"101" .$ always (BP:GPReg16)
||| #b"110" .$ always (SI:GPReg16)
||| #b"111" .$ always (DI:GPReg16).

Definition VRegCodec rexBit s : Codec (GPReg s) :=
  match s return Codec (GPReg s) with
  | OpSize1 => Reg8Codec rexBit
  | OpSize2 => GPReg16Codec rexBit
  | OpSize4 => GPReg32Codec rexBit
  | OpSize8 => GPReg64Codec rexBit
  end.

Definition VWORDCodec s : Codec (VWORD s) :=
  match s with
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

Definition scaleCast : CAST (BITS 2) Scale.
apply: MakeCast decScale (fun x => Some (encScale x)) _.
move => x y [<-]; by rewrite encScaleK. Defined.
Definition scaleCodec : Codec Scale := bitsCodec 2 ~~> scaleCast.

Definition conditionCast : CAST (BITS 3) Condition.
apply: MakeCast decCondition (fun x => Some (encCondition x)) _.
move => x y [<-]; by rewrite encConditionK. Defined.
Definition conditionCodec : Codec Condition := bitsCodec 3 ~~> conditionCast.

Definition SIBCast a : CAST (Scale * option (IxReg a) * option (BaseReg a)) (option (BaseReg a) * option (IxReg a * Scale)).
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
Definition SIBCodec a X B := 
  scaleCodec $ SIBIxRegCodec a X $ (SIBBaseRegCodec a B ~~> unSome) ~~> SIBCast a.  

Definition SIB00Codec a X B := 
  scaleCodec $ SIBIxRegCodec a X $ (NonBPBaseRegCodec a B ~~> unSome) ~~> SIBCast a.

Definition SIB00NoBaseCodec a X :=
  scaleCodec $ SIBIxRegCodec a X $ #b"101" .$ alwaysNone ~~> SIBCast a.

Definition tryEqAdSize F (a1 a2: AdSize): F a1 -> option (F a2) :=
  match a1, a2 with
  | AdSize4, AdSize4 => fun x => Some x
  | AdSize8, AdSize8 => fun x => Some x
  | _, _ => fun x => None
  end. 

Definition RIPrelCast s (a:AdSize) : CAST DWORD (RegMem s).
apply: (MakeCast (fun offset => RegMemM s a (RIPrel _ offset))
                (fun rm => if rm is RegMemM a' (RIPrel offset)
                           then @tryEqAdSize _ a' a offset else None) _).
case a; do 3 elim => //; by move => ? ? [->]. 
Defined. 

Definition mkMemSpecCast (seg: option SegReg) s (a:AdSize) : 
  CAST (option (BaseReg a) * option (IxReg a * Scale) * DWORD) (RegMem s). 
apply:
  (MakeCast (fun p => let: (b,i,d) := p in RegMemM s a (mkMemSpec a seg b i d))
  (fun rm => if rm is RegMemM a' (mkMemSpec seg' b i d)
             then if seg==seg' then @tryEqAdSize (fun a => (option (BaseReg a) * option (IxReg a * Scale) * DWORD)%type) a' a (b,i,d) 
             else None else None) _).
case a. 
- elim => //. elim => //. elim => //. move => seg' b i d [[b' i'] d']. 
  case E: (seg == seg') => //. rewrite (eqP E). by move => [<- <- <-]. 
- elim => //.  move => seg' b i d [[b' i'] d']. by case: (seg == seg') => //. 
- elim => //. elim => //. elim => //. move => seg' b i d [[b' i'] d']. by case: (seg == seg') => //. 
- elim => //. move => seg' b i d [[b' i'] d']. 
  case E: (seg == seg') => //. rewrite (eqP E). by move => [<- <- <-]. 
Defined. 

(* See Table 2-2 and 2-3 for details *)
Definition RegMemCodec T (seg: option SegReg) (a:AdSize) (R X B:bool) (regOrOpcodeCodec : Codec T) s : Codec (T * RegMem s) :=

(* RIP-relative addressing. See Table 2-7 *)
(* NOTE: in 32-bit mode this is used for pure displacement *)
    #b"00" .$ regOrOpcodeCodec $ #b"101" .$ (DWORDCodec ~~> RIPrelCast s a)

(* Mod R/M with mod=00: no displacement *)
||| #b"00" .$ regOrOpcodeCodec $ ((NonBPNonSPBaseRegCodec a B ~~> unSome) $ alwaysNone $ always #0 ~~> mkMemSpecCast seg s a)
(* SIB with mod=00: no displacement *)
||| #b"00" .$ regOrOpcodeCodec $ (#b"100" .$ SIB00Codec a X B $ always #0 ~~> mkMemSpecCast seg s a)
||| #b"00" .$ regOrOpcodeCodec $ (#b"100" .$ SIB00NoBaseCodec a X $ DWORDCodec ~~> mkMemSpecCast seg s a)

(* Mod R/M with mod=01: disp8 *)
||| #b"01" .$ regOrOpcodeCodec $ ((NonSPBaseRegCodec a B ~~> unSome) $ alwaysNone $ shortDWORDCodec ~~> mkMemSpecCast seg s a)
(* SIB with mod=01: disp8 *)
||| #b"01" .$ regOrOpcodeCodec $ (#b"100" .$ SIBCodec a X B $ shortDWORDCodec ~~> mkMemSpecCast seg s a)

(* Mod R/M with mod=10: disp32 *)
||| #b"10" .$ regOrOpcodeCodec $ ((NonSPBaseRegCodec a B ~~> unSome) $ alwaysNone $ DWORDCodec ~~> mkMemSpecCast seg s a)
(* SIB with mod=10: disp32 *)
||| #b"10" .$ regOrOpcodeCodec $ (#b"100" .$ SIBCodec a X B $ DWORDCodec ~~> mkMemSpecCast seg s a)

(* Mod R/M with mod=11: reg-reg *)
||| #b"11" .$ regOrOpcodeCodec $ (VRegCodec B s ~~> unRegMemR s).





Definition RegMemOpCodec seg (a:AdSize) R X B (op: BITS 3) dword :=
  RegMemCodec seg a R X B (Const op) dword ~~> sndUnitCast _.

Definition mkOpSize p W b := 
  if b then
    if W then OpSize8 else if p then OpSize2 else OpSize4 
  else OpSize1.

Definition unDstSrcRMR s : CAST (GPReg s * RegMem s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s p.1 y
                              | RegMemM a y => DstSrcRM s a p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM a x y => Some (x,RegMemM _ a y)
                              | _ => None end) _).
elim => //.  
- by move => ? ? [? ?] [<- <-]. 
- by move => ? ? ? [? ?] [<-] [<-]. 
Defined. 

Definition unDstSrcMRR s : CAST (GPReg s * RegMem s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR s y p.1
                              | RegMemM a y => DstSrcMR s a y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR a x y => Some (y, RegMemM _ a x)
                              | _ => None end) _).
elim => //. 
- by move => ? ? [? ?] [<-] <-. 
- by move => ? ? ? [? ?] [<- <-]. 
Defined.

Definition unDstSrcMRI s : CAST (RegMem s * IMM s) (DstSrc s).
apply: (MakeCast
       (fun p => match p.1 with RegMemR y => (DstSrcRI s y p.2)
                              | RegMemM a y => (DstSrcMI s a y p.2) end)
       (fun ds => match ds with DstSrcRI x y => Some (RegMemR _ x, y)
                              | DstSrcMI a x y => Some (RegMemM _ a x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? ? [<- ->]. Defined.

Definition unDstSrcRI s : CAST (GPReg s * IMM s) (DstSrc s).
  admit.
  (*
apply: (MakeCast (fun p => DstSrcRI _ p.1 p.2)
       (fun ds => match ds with DstSrcRI x y => Some (x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. *) Defined.

Definition unMovDstSrcRMR s : CAST (GPReg s * RegMem s) (MovDstSrc s).
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

(*---------------------------------------------------------------------------
    Casts for instructions
  ---------------------------------------------------------------------------*)
Definition prefAndOpSizeToBool (w: bool) (os: OpSize) :=  
  match os, w with
  | OpSize4, false => Some true
  | OpSize2, true => Some true
  | OpSize1, _ => Some false  
  | _, _ => None
  end.

Definition sizesPrefixCodec X (c : bool -> bool -> AdSize -> Codec X) : Codec X :=
    #x"66" .$ #x"67" .$ (c true false AdSize4)
||| #x"67" .$ #x"66" .$ (c true false AdSize4)
||| #x"67" .$ (c false false AdSize4)
||| #x"66" .$ (c true false AdSize8)
||| #x"F3" .$ (c false true AdSize8)
||| c false false AdSize8.

Definition opSizePrefixCodec X (c : bool -> Codec X) : Codec X :=
    #x"66" .$ (c true)
||| c false.

Definition adSizePrefixCodec X (c : AdSize -> Codec X) : Codec X :=
    #x"67" .$ (c AdSize4)
||| c AdSize8.

(* REX prefix format, as described in section 2.2.1.2 *)
Definition rexPrefixCodec X (c: bool -> bool -> bool -> bool -> Codec X) : Codec X :=
    #b"0100" .$ Cond (fun W => Cond (fun R => Cond (fun X => Cond (fun B =>
    c W R X B))))
||| c false false false false.

Definition segPrefixCodec X (f:option SegReg -> Codec X) : Codec X :=
    #x"2E" .$ f (Some CS)
||| #x"36" .$ f (Some SS)
||| #x"3E" .$ f (Some DS)
||| #x"26" .$ f (Some ES)
||| #x"64" .$ f (Some FS)
||| #x"65" .$ f (Some GS)
||| f None.


Definition isHLT : CAST unit Instr.
  admit.
  (*
apply: MakeCast (fun _ => HLT) (fun i => if i is HLT then Some tt else None) _; by elim; elim. *)
Defined.

Definition shortQWORDEmb : CAST BYTE QWORD.
  admit.
  (*
apply: MakeCast (@signExtend _ 7) (@signTruncate _ 7) _.
Proof. move => d b/= H. by apply signTruncateK. *)
Defined.

Definition longQWORDEmb : CAST DWORD QWORD.
  admit.
  (*
apply: MakeCast (@signExtend _ 31) (@signTruncate _ 31) _.
Proof. move => d b/= H. by apply signTruncateK. *)
Defined.

Definition shortDWORDCodec: Codec DWORD :=
  BYTECodec ~~> shortDWORDEmb.
Definition shortQWORDCodec: Codec QWORD :=
  BYTECodec ~~> shortQWORDEmb.
Definition longQWORDCodec: Codec QWORD :=
  DWORDCodec ~~> longQWORDEmb.

Definition ShortTgtCodec a : Codec (Tgt a) :=
(match a as a return Codec (VWORD (adSizeToOpSize a)) with
| AdSize4 => shortDWORDCodec
| AdSize8 => shortQWORDCodec
end) ~~> unTgt a.

Definition DWORDTgtCodec a : Codec (Tgt a) := 
(match a as a return Codec (VWORD (adSizeToOpSize a)) with
| AdSize4 => DWORDCodec
| AdSize8 => longQWORDCodec
end) ~~> unTgt a.

Definition VAXCodec s : Codec (GPReg s) :=
match s return Codec (GPReg s) with
| OpSize1 => always (AL:Reg8)
| OpSize2 => always (AX:GPReg16)
| OpSize4 => always (EAX:GPReg32)
| OpSize8 => always (RAX:GPReg64)
end.

Definition opcodeWithSizeCodec X (opcode:BYTE) (c : bool -> Codec X) : Codec X :=
  droplsb opcode .$ Cond c.

(*---------------------------------------------------------------------------
    TEST instruction
  ---------------------------------------------------------------------------*)
Definition tryEqOpSize F (s1 s2: OpSize): F s1 -> option (F s2) :=
  match s1, s2 with
  | OpSize1, OpSize1 => fun x => Some x
  | OpSize2, OpSize2 => fun x => Some x
  | OpSize4, OpSize4 => fun x => Some x
  | OpSize8, OpSize8 => fun x => Some x
  | _, _ => fun x => None
  end. 

Definition unTEST s : CAST (RegMem s * RegImm s) Instr.
apply (MakeCast (fun p => TESTOP s p.1 p.2)
                (fun i => if i is TESTOP s1 x d
  then tryEqOpSize (F:= fun s=> (RegMem s * RegImm s)%type) s (x,d) else None)). 
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined.

Definition TESTCodec :=
  segPrefixCodec (fun seg => 
  sizesPrefixCodec (fun w r a =>
  rexPrefixCodec (fun W R X B =>
    (* Short form for TEST AL/AX/EAX/RAX, imm8/imm16/imm32 *)
        opcodeWithSizeCodec #x"A8" (fun d => 
        (VAXCodec (mkOpSize w W d) ~~> unRegMemR _) $ (IMMCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, imm8 | TEST r/m16, imm16 | TEST r/m32, imm32 | TEST r/m64, imm32 *)
    ||| opcodeWithSizeCodec #x"F6" (fun d =>
        RegMemOpCodec seg a R X B #0 (mkOpSize w W d) $ (IMMCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, r8 | TEST r/m16, r16 | TEST r/m32, r32 | TEST r/m64, r64 *)
    ||| opcodeWithSizeCodec #x"84" (fun d =>
        RegMemCodec seg a R X B (VRegCodec R _ ~~> unRegImmR _) _ ~~> swapPairCast _ _ ~~> unTEST (mkOpSize w W d))
    ))).

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
Definition unJMP a : CAST (JmpTgt a) Instr. 
apply: (MakeCast (JMPrel a) (fun i => if i is JMPrel a' t 
  then @tryEqAdSize (fun a => (JmpTgt a)) a' a t else None) _).
by case: a; case => //; case => // ? ? [->]. 
Defined.

(* This is an example of a codec that is mode-dependent: the DEFAULT for 64-bit mode is 64-bit,
  with or without a rex prefix *)
Definition JMPCodec :=
    #x"EB" .$ ShortTgtCodec _ ~~> unJmpTgtI _ ~~> unJMP AdSize8
||| #x"E9" .$ DWORDTgtCodec _ ~~> unJmpTgtI _ ~~> unJMP AdSize8
||| segPrefixCodec (fun seg =>
    adSizePrefixCodec (fun a =>
    rexPrefixCodec (fun W R X B =>
    #x"FF" .$ RegMemOpCodec seg a R X B #4 (adSizeToOpSize a) ~~> unJmpTgtRM a ~~> unJMP a))).

(*---------------------------------------------------------------------------
    CALL instruction
    @TODO: 16-bit variants, far calls
  ---------------------------------------------------------------------------*)
Definition unCALL a : CAST (JmpTgt a) Instr.
apply: MakeCast (CALLrel a) (fun i => if i is CALLrel a' t 
  then @tryEqAdSize (fun a => (JmpTgt a)) a' a t else None) _.
by case: a; case => //; case => // ? ? [->]. 
Defined.

Definition CALLCodec :=
    #x"E8" .$ DWORDTgtCodec _ ~~> unJmpTgtI _ ~~> unCALL AdSize8
||| segPrefixCodec (fun seg =>
    adSizePrefixCodec (fun a =>
    rexPrefixCodec (fun W R X B =>
    #x"FF" .$ RegMemOpCodec seg a R X B #2 (adSizeToOpSize a) ~~> unJmpTgtRM a ~~> unCALL _))).


(*---------------------------------------------------------------------------
    JCC instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unJCC : CAST (Condition*bool*Tgt AdSize8) Instr.
apply: (MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _).
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.

Definition JCCCodec :=
    #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ DWORDTgtCodec AdSize8 ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec AdSize8  ~~> unJCC.

(*---------------------------------------------------------------------------
    SET instruction
  ---------------------------------------------------------------------------*)
Definition unSET : CAST (Condition*bool*GPReg OpSize1) Instr.
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
Definition unPUSH s : CAST (Src s) Instr.
apply (MakeCast (@PUSH s) 
                (fun i => if i is PUSH s1 x then tryEqOpSize (F:=Src) s x else None)).  
elim: s. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  move => r. elim => //. by move => r' [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  move => r. elim => //. by move => r' [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  move => r. elim => //. by move => r' [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  move => r. elim => //. by move => r' [<-]. 
Defined. 

Definition PUSHCodec := 
  (sizesPrefixCodec (fun w r a =>
   rexPrefixCodec (fun W R X B =>
       (#x"68" .$ IMMCodec _ ~~> unSrcI _
(*    ||| #x"6A" .$ shortDWORDCodec ~~> unSrcI _ *)
    ||| #b"01010" .$ VRegCodec R _ ~~> unSrcR _) ~~> unPUSH (mkOpSize w W false))))
(*||| segPrefixCodec (fun seg =>
    #x"FF" .$ RegMemOpCodec seg AdSize4 false false false #6 _ ~~> unSrcRM ~~> unPUSH)*)
.

(*---------------------------------------------------------------------------
    POP instruction
  ---------------------------------------------------------------------------*)
Definition unPOP s : CAST (RegMem s) Instr.
apply (MakeCast (@POP s) 
                (fun i => if i is POP s1 x then tryEqOpSize (F:=RegMem) s x else None)).  
elim: s. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
  do 2 elim => //. elim => //. move => c; elim => //; by move => c' [->].  
  by move => a ms src [<-]. 
Defined. 

Definition POPCodec :=
  (segPrefixCodec (fun seg =>
   sizesPrefixCodec (fun w r a =>
   rexPrefixCodec (fun W R X B =>
   #x"8F" .$ RegMemOpCodec seg AdSize4 R X B #0 _ ~~> unPOP (mkOpSize w W false)))))
(* @TODO: 16-bit and 32-bit register versions *)
||| #b"01011" .$ GPReg64Codec false ~~> unRegMemR OpSize8 ~~> unPOP OpSize8.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)

Definition unMOV w W d : CAST (MovDstSrc (mkOpSize w W d)) Instr.
apply (MakeCast (MOVOP _) (fun i => if i is MOVOP _ d then tryEqOpSize _ d else None)). 
by elim:w; elim:d; elim:W; elim => //; elim => //; move => ? src [->]. 
Defined. 

Definition MOVCodec :=  
  segPrefixCodec (fun seg =>
  sizesPrefixCodec (fun w r a =>
  rexPrefixCodec (fun W R X B =>
      (* MOV r/m8, r8 | MOV r/m16, r16 | MOV r/m32, r32 *)
      opcodeWithSizeCodec #x"88" (fun d =>
        RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unMovDstSrcMRR _ ~~> unMOV w W d)
      (* MOV r8, r/m8 | MOV r16, r/m16 | MOV r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"8A" (fun d =>   
        RegMemCodec seg a R X B (VRegCodec R _) _  ~~> unMovDstSrcRMR _ ~~> unMOV w W d)
(*
      (* MOV r/m8, imm8 | MOV r/m16, imm16 | MOV r/m32, imm32 *)
  ||| opcodeWithSizeCodec #x"C6" (fun d =>
        RegMemOpCodec a R X B #0 _ $ IMMCodec _ ~~> unMovDstSrcMRI _ ~~> unMOV w d)
*)

      (* TODO: get this right. It takes a full 64-bit immediate! *)
      (* MOV r8, imm8 | MOV r16, imm16 | MOV r32, imm32 | MOV r64, imm64 *)
  ||| #x"B" .$ Cond (fun d => 
        VRegCodec R _ $ VWORDCodec _ ~~> unMovDstSrcRI _ ~~> unMOV w W d)))).

(*---------------------------------------------------------------------------
    MOVX instruction
  ---------------------------------------------------------------------------*)

Definition unMOVZX : CAST (GPReg32 * RegMem OpSize1) Instr.
  refine (MakeCast (fun v => MOVX false v.1 v.2) 
                   (fun i => if i is MOVX false v1 v2
                             then Some (v1, v2)
                             else None) _).
  case=> x //=;
  case: x => dst src [_ _] //= [<- <-] //.
Defined.


Definition MOVZXCodec :=
  sizesPrefixCodec (fun w r a =>
  rexPrefixCodec (fun W R X B =>
  #x"0FB6" .$  RegMemCodec None a R X B (VRegCodec R OpSize4) OpSize1 ~~> unMOVZX)).

(*---------------------------------------------------------------------------
    BT, BTC, BTR, BTS instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unBITOPR : CAST (BitOp * (GPReg32 * RegMem OpSize4)) Instr.
apply: (MakeCast (fun p => let: (op,(r,rm)) := p in BITOP op rm (inl r))
                (fun i => if i is BITOP op y (inl r) then Some(op,(r,y)) else None) _).
elim => //. move => op dst src [op' [dst' src']]. case src => // r. by move => [-> -> ->].
Defined.

Definition unBITOPI : CAST (BitOp * RegMem OpSize4 * BYTE) Instr.
apply: (MakeCast (fun p => let: (op,rm,b) := p in BITOP op rm (inr b))
                (fun i => if i is BITOP op y (inr b) then Some(op,y,b) else None) _).
elim => //. move => op dst src [[op' dst'] src']. case src => // r. by move => [-> -> ->].
Defined.

Definition BITCodec :=
    segPrefixCodec (fun seg =>
    #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec seg AdSize4 false false false (GPReg32Codec false) _) ~~> unBITOPR
||| #x"0F" .$ #x"BA" .$ RegMemCodec seg AdSize4 false false false (#b"1" .$ bitOpCodec) _ $ BYTECodec ~~> unBITOPI).


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

Definition unSHIFT s : CAST (ShiftOp * RegMem s * ShiftCount) Instr.
eapply (MakeCast (fun p => let: (op,v,count) := p in SHIFTOP _ op v count)
                 (fun i => if i is SHIFTOP s1 op v count 
  then tryEqOpSize (F:= fun s=> (ShiftOp*RegMem s*ShiftCount)%type) s (op,v,count) else None)).
elim:s; elim => //; elim => //; move => ? ? src [[? ?] ?]; by move => [-> -> ->]. 
Defined.

Definition SHIFTCodec :=  
  segPrefixCodec (fun seg =>
  sizesPrefixCodec (fun w r a => 
    (
      opcodeWithSizeCodec #x"C0" (fun d => 
        RegMemCodec seg a false false false shiftOpCodec (mkOpSize w false d) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D0" (fun d =>
        RegMemCodec seg a false false false shiftOpCodec (mkOpSize w false d) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D2" (fun d =>
        RegMemCodec seg a false false false shiftOpCodec (mkOpSize w false d) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT _)
    )
  )).

(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
Definition unBOP s : CAST (BinOp * DstSrc s) Instr.
apply: (MakeCast (fun p => BOP _ p.1 p.2))
                 (fun i => if i is BOP s1 op v 
                  then tryEqOpSize (F:=fun s => (BinOp*DstSrc s)%type) s (op,v) else None) _.  elim:s; elim => //; elim => //; move => ? src [? ?]; by move => [-> ->]. 
Defined.

Definition shortVWORDEmb w : CAST BYTE (VWORD (if w then OpSize2 else OpSize4)).
  admit.
  (*
destruct w. 
apply: MakeCast (@signExtend 8 7) (@signTruncate 8 7) _.
- move => d b/= H. by apply signTruncateK. 
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
- move => d b/= H. by apply signTruncateK. 
*)
Defined.

Definition shortVWORDCodec w: Codec _ :=
  BYTECodec ~~> shortVWORDEmb w.

Definition BINOPCodec :=
    segPrefixCodec (fun seg =>
    sizesPrefixCodec (fun w r a => 
    rexPrefixCodec (fun W R X B =>
      (* OP AL, imm8 | OP AX, imm16 | OP EAX, imm32 | OP RAX, imm32 *)
    #b"00" .$ opCodec $ #b"100" .$ 
      (VAXCodec _ $ IMMCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"101" .$ 
      (VAXCodec _ $ IMMCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w W true)

    (* OP r/m8, r8 | OP r/m16, r16 | OP r/m32, r32 | OP r/m64, r64 *)
||| #b"00" .$ opCodec $ #b"010" .$ 
      (RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"011" .$ 
      (RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w W true)

    (* OP r8, r/m8 | OP r16, r/m16 | OP r32, r/m32 | OP r64, r/m64 *)
||| #b"00" .$ opCodec $ #b"000" .$ 
      (RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w W false)
||| #b"00" .$ opCodec $ #b"001" .$ 
      (RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w W true)

    (* OP r/m8, imm8 | OP r/m16, imm16 | OP r/m32, imm32 | OP r/m64, imm32 *)
||| opcodeWithSizeCodec #x"80" (fun d => RegMemCodec seg a R X B opCodec _ $ IMMCodec _
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP (mkOpSize w W d))

(*
    (* OP r/m16, imm8 | OP r/m32, imm8 (sign-extended) *)
||| #x"83" .$ (RegMemCodec opCodec _ $ shortVWORDCodec w) 
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP _ 
*)
    )))
.

(*---------------------------------------------------------------------------
    INC/DEC/NOT/NEG instructions
  ---------------------------------------------------------------------------*)
Definition unINC s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_INC v)
                (fun i => if i is UOP s1 OP_INC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unDEC s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_DEC v)
                (fun i => if i is UOP s1 OP_DEC v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNEG s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NEG v)
                (fun i => if i is UOP s1 OP_NEG v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition unNOT s : CAST (RegMem s) Instr.
apply: MakeCast (fun v => UOP _ OP_NOT v)
                (fun i => if i is UOP s1 OP_NOT v then tryEqOpSize s v else None) _.
elim: s; elim => //; elim => op src q; destruct op => H; by inversion H. Defined.

Definition UOPCodec :=
  segPrefixCodec (fun seg =>
  sizesPrefixCodec (fun w r a => 
  rexPrefixCodec (fun W R X B =>
    opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec seg a R X B #0 _ ~~> unINC (mkOpSize w false d))

||| opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec seg a R X B #1 _ ~~> unDEC (mkOpSize w false d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec seg a R X B #2 _ ~~> unNOT (mkOpSize w false d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec seg a R X B #3 _ ~~> unNEG (mkOpSize w false d))

(* @TODO: make these available only in 32-bit mode; in 64-bit mode these are REX prefixes *)
(*
||| INCPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unINC (mkOpSize w false false)
||| DECPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unDEC (mkOpSize w false false)
*)
  ))).


(*---------------------------------------------------------------------------
    MUL and IMUL instructions
  ---------------------------------------------------------------------------*)

Definition unImulDstSrcRM s : CAST (RegMem s) (ImulDstSrc s).
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

Definition unImulDstSrcRRM s : CAST (GPReg s * RegMem s) (ImulDstSrc s).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => (ImulDstSrcRR s p.1 y)
                              | RegMemM a y => (ImulDstSrcRM s a p.1 y) end)
       (fun ds => match ds with ImulDstSrcRR x y => Some (x, RegMemR _ y)
                              | ImulDstSrcRM a x y => Some (x, RegMemM _ a y)
                              | _ => None end) _).
case=> x //.
- by move=> src [? ?] [<-] [<-].
- by move=> dst src [? ?] [<-] [<-].
Defined.

Definition unImulDstSrcRRMI s : CAST (GPReg s * RegMem s * IMM s) (ImulDstSrc s).
apply: (MakeCast
       (fun p => match p.1.2 with RegMemR y => (ImulDstSrcRRI s p.1.1 y p.2)
                                | RegMemM a y => (ImulDstSrcRMI s a p.1.1 y p.2) end)
       (fun ds => match ds with ImulDstSrcRRI x y i => Some (x, RegMemR _ y, i)
                              | ImulDstSrcRMI a x y i => Some (x, RegMemM _ a y, i)
                              | _ => None end) _).
case=> x //.
- by move=> src c [? ?] [<-] [<-].
- by move=> dst src c [? ?] [<-] [<-].
Defined.

Definition unIMUL w W d : CAST (ImulDstSrc (mkOpSize w W d)) Instr.
  apply: (MakeCast (fun p => IMUL _ p) 
                   (fun i => if i is IMUL _ p then
                               tryEqOpSize (mkOpSize w W d) p
                             else None) _).
  case: w; case: W; case: d; case=> //; case=> //= ? ? [<-] //=.
Defined.

Definition unMUL s : CAST (RegMem s) Instr.
apply: (MakeCast (@MUL s)
                 (fun i => if i is MUL s1 v 
                  then tryEqOpSize s v else None) _).  
case: s; case=> //; case=> //= q ? [<-] //.
Defined.

Definition MULCodec :=
  segPrefixCodec (fun seg =>
  sizesPrefixCodec (fun w r a => 
  rexPrefixCodec (fun W R X B =>
  (*  IMUL r16, r/m16 | IMUL r32, r/m32 | IMUL r64, r/m64 *)
  (#x"0FAF" .$ (RegMemCodec seg a R X B (VRegCodec R _) _ ~~>  unImulDstSrcRRM _)
   ~~> unIMUL w W false)
  (* IMUL r16, r/m16, imm16 | IMUL r32, r/m32, imm32 | IMUL r64, r/m64, imm32 *)
||| #x"69" .$ 
     (RegMemCodec seg a R X B (VRegCodec R _) _ $
      IMMCodec _ ~~>  unImulDstSrcRRMI _) ~~> (unIMUL  w W false))
  (* MUL r/m8 | MUL r/m16 | MUL r/m32 *)
||| opcodeWithSizeCodec #x"F6" (fun d =>  
    RegMemOpCodec seg a false false false #4 _ ~~> unMUL (mkOpSize w false d)))).


(*---------------------------------------------------------------------------
    LEA instruction 
  ---------------------------------------------------------------------------*)
Definition unLEA s : CAST (GPReg s * RegMem s) Instr.
apply: (MakeCast (fun p => LEA s p.1 p.2) (fun i => if i is LEA s' x y then 
  tryEqOpSize (F:= fun s=> (GPReg s * RegMem s)%type) s (x,y) else None) _).
by elim: s; elim => //; elim => //; move => r q [a b] [-> <-]. Defined.

Definition LEACodec :=
  segPrefixCodec (fun seg =>
  sizesPrefixCodec (fun w r a =>     
  rexPrefixCodec (fun W R X B =>
  #x"8D" .$ RegMemCodec seg a R X B (VRegCodec R _) _ ~~> unLEA (mkOpSize w W true)))).

(*---------------------------------------------------------------------------
    XCHG instruction 
  ---------------------------------------------------------------------------*)
Definition unXCHG s : CAST (GPReg s * RegMem s) Instr. 
  apply: MakeCast (fun p => XCHG s p.1 p.2) 
  (fun i => if i is XCHG s1 x y 
            then tryEqOpSize (F:=fun s => (GPReg s * RegMem s)%type) s (x,y) else None) _.  
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


Definition unMOVABS : CAST (GPReg64 * QWORD) Instr.
  refine (MakeCast (fun (p: GPReg64 * QWORD) => let (r, i) := p in MOVABS r i)
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
Definition unXMem : CAST (RegMem OpSize8) XMem. 
refine (MakeCast
          (fun p: RegMem OpSize8  => match p with
                      | RegMemM a m => XMemM a m
                      | RegMemR (mkGPReg64 RAX) => XMemR XMM0
                      | RegMemR (mkGPReg64 RBX) => XMemR XMM1
                      | RegMemR (mkGPReg64 RCX) => XMemR XMM2
                      | RegMemR (mkGPReg64 RDX) => XMemR XMM3
                      | RegMemR (mkGPReg64 RSI) => XMemR XMM4
                      | RegMemR (mkGPReg64 RDI) => XMemR XMM5
                      | RegMemR RSP => XMemR XMM6
                      | RegMemR (mkGPReg64 RBP) => XMemR XMM7
                      | RegMemR (mkGPReg64 R8) => XMemR XMM8
                      | RegMemR (mkGPReg64 R9) => XMemR XMM9
                      | RegMemR (mkGPReg64 R10) => XMemR XMM10
                      | RegMemR (mkGPReg64 R11) => XMemR XMM11
                      | RegMemR (mkGPReg64 R12) => XMemR XMM12
                      | RegMemR (mkGPReg64 R13) => XMemR XMM13
                      | RegMemR (mkGPReg64 R14) => XMemR XMM14
                      | RegMemR (mkGPReg64 R15) => XMemR XMM15 end)
          (fun p => match p with
                      | XMemM a m => Some (RegMemM _ a m)
                      | XMemR XMM0 => Some (RegMemR OpSize8 (mkGPReg64 RAX)) 
                      | XMemR XMM1 => Some (RegMemR OpSize8 (mkGPReg64 RBX)) 
                      | XMemR XMM2 => Some (RegMemR OpSize8 (mkGPReg64 RCX)) 
                      | XMemR XMM3 => Some (RegMemR OpSize8 (mkGPReg64 RDX)) 
                      | XMemR XMM4 => Some (RegMemR OpSize8 (mkGPReg64 RSI)) 
                      | XMemR XMM5 => Some (RegMemR OpSize8 (mkGPReg64 RDI)) 
                      | XMemR XMM6 => Some (RegMemR OpSize8 RSP) 
                      | XMemR XMM7 => Some (RegMemR OpSize8 (mkGPReg64 RBP)) 
                      | XMemR XMM8 => Some (RegMemR OpSize8 (mkGPReg64 R8)) 
                      | XMemR XMM9 => Some (RegMemR OpSize8 (mkGPReg64 R9)) 
                      | XMemR XMM10 => Some (RegMemR OpSize8 (mkGPReg64 R10)) 
                      | XMemR XMM11 => Some (RegMemR OpSize8 (mkGPReg64 R11)) 
                      | XMemR XMM12 => Some (RegMemR OpSize8 (mkGPReg64 R12)) 
                      | XMemR XMM13 => Some (RegMemR OpSize8 (mkGPReg64 R13)) 
                      | XMemR XMM14 => Some (RegMemR OpSize8 (mkGPReg64 R14)) 
                      | XMemR XMM15 => Some (RegMemR OpSize8 (mkGPReg64 R15)) 
                    end) _).
case=> //. 
- by case=> //; case=> // ? [<-].
- by move=> ? ? ? [<-].
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
  sizesPrefixCodec (fun w r a =>
  rexPrefixCodec (fun W R X B =>
  (* MOVQ xmm1, xmm2/m64
     Prefix: F3 
     TODO: is that enforced? *)
  #x"0F7E" .$ 
   RegMemCodec  None a R X B (XMMregCodec R) _ ~~> 
   pairOfCasts (idCast _) unXMem ~~>
   unXmmdstsrcXRM ~~> 
   unMOVQ
||| (* MOVQ xmm2/m64, xmm1 
    Prefix: 66, TODO: is that enforced ? *)
  #x"0FD6" .$ 
   RegMemCodec  None a R X B (XMMregCodec R) _ ~~> 
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
||| JMPCodec ||| CALLCodec ||| TESTCodec ||| PUSHCodec ||| POPCodec ||| RETCodec
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