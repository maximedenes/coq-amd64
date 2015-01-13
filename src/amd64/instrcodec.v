(*======================================================================================
  Instruction codec
  ======================================================================================*)
From Ssreflect
     Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple.
Require Import bitsrep bitsops.
Require Import cast codec bitscodec.
Require Import amd64.instr amd64.instrsyntax (*amd64.encdechelp*) amd64.reg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*---------------------------------------------------------------------------
    Casts for datatypes used in instructions
  ---------------------------------------------------------------------------*)

(*
Definition unSrcR : CAST Reg Src.
apply: MakeCast SrcR (fun s => if s is SrcR r then Some r else None) _.
by elim; congruence. Defined.

Definition unSrcI : CAST DWORD Src.
apply: MakeCast SrcI (fun s => if s is SrcI i then Some i else None) _.
by elim; congruence. Defined.

Definition unRegMemR d : CAST (VReg d) (RegMem d).
apply: MakeCast (RegMemR d) (fun rm => if rm is RegMemR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmR d : CAST (VReg d) (RegImm d).
apply: MakeCast (RegImmR d) (fun rm => if rm is RegImmR r then Some r else None) _.
by elim; congruence. Defined.

Definition unRegImmI d : CAST (VWORD d) (RegImm d).
apply: MakeCast (RegImmI d) (fun rm => if rm is RegImmI v then Some v else None) _.
by elim; congruence. Defined.

Definition unJmpTgtI : CAST Tgt JmpTgt.
apply: MakeCast JmpTgtI (fun t => if t is JmpTgtI d then Some d else None) _.
elim; elim; congruence. Defined.

Definition unJmpTgtRM : CAST (RegMem OpSize4) JmpTgt.
apply: (MakeCast (fun (rm:RegMem OpSize4) => match rm with RegMemR r => JmpTgtR r | RegMemM m => JmpTgtM m end)
  (fun i => match i with JmpTgtR r => Some (RegMemR OpSize4 r) | JmpTgtM m => Some (RegMemM OpSize4 m) | _ => None end) _).
elim => //. move => m. elim => // ms. by move => [<-].
by move => r y [<-].
Defined.

Definition unTgt : CAST DWORD Tgt.
apply: MakeCast mkTgt (fun t => let: mkTgt d := t in Some d) _.
by move => [d] y [<-].
Defined.

Definition unSrcRM : CAST (RegMem OpSize4) Src.
apply: MakeCast
  (fun (rm: RegMem OpSize4) => match rm with RegMemR r => SrcR r | RegMemM m => SrcM m end)
  (fun i => match i with SrcR r => Some (RegMemR OpSize4 r) | SrcM m => Some (RegMemM _ m)
                       | _ => None
            end) _.
elim => //; by move => ? ? [<-]. Defined.

(*---------------------------------------------------------------------------
    Casts and codecs for bit-encoded types e.g. registers, scales, conditions
  ---------------------------------------------------------------------------*)
 *)


Definition allNonSPReg: 16.-tuple (option nonSPReg)
  := [tuple Some RAX; Some RCX; Some RDX; Some RBX;
            None;     Some RBP; Some RSI; Some RDI;
            Some R8;  Some R9; Some R10; Some R11;
            None;     Some R13; Some R14; Some R15].

Definition decNonSPReg (b: bool * BITS 3) := tnth allNonSPReg (toZp (joinmsb b)).
Definition encNonSPReg (r: nonSPReg) : bool * BITS 3 :=
  match r with
  | RAX => (false, #b"000")
  | RCX => (false, #b"001")
  | RDX => (false, #b"010")
  | RBX => (false, #b"011")
  | RBP => (false, #b"101")
  | RSI => (false, #b"110")
  | RDI => (false, #b"111")
  | R8  => (true, #b"000")
  | R9  => (true, #b"001")
  | R10 => (true, #b"010")
  | R11 => (true, #b"011")
  | R13 => (true, #b"101")
  | R14 => (true, #b"110")
  | R15 => (true, #b"111")
  end.
Lemma encNonSPRegK : pcancel encNonSPReg decNonSPReg. Proof. by case. Qed.
Canonical Structure NonSPRegEqMixin := PcanEqMixin encNonSPRegK.
Canonical Structure NonSPRegEqType := Eval hnf in EqType _ NonSPRegEqMixin.
(*Instance NonSPRegEMB: EMB _ _ := PEmb encNonSPRegK.*)
(*Coercion injNonSPReg := (@inj _ _ NonSPRegEMB). *)

Definition nonBPnonSPRegCodec (rex: bool) : Codec nonSPReg :=
  if rex then
    #b"000" .$ always R8
||| #b"001" .$ always R9
||| #b"010" .$ always R10
||| #b"011" .$ always R13
||| #b"110" .$ always R14
||| #b"111" .$ always R15
  else
    #b"000" .$ always RAX
||| #b"001" .$ always RCX
||| #b"010" .$ always RDX
||| #b"011" .$ always RBX
||| #b"110" .$ always RSI
||| #b"111" .$ always RDI.

Definition nonSPRegCodec (rex: bool) : Codec nonSPReg :=
    nonBPnonSPRegCodec rex
||| (if rex then
       #b"101" .$ always R13
     else
       #b"101" .$ always RBP).

(* TODO: factorize with nonSPregCodec *)
Definition optionalNonSPregCast: CAST (bool * BITS 3) (option nonSPReg).
  apply: MakeCast (fun (x: bool * BITS 3) => decNonSPReg x)
                  (fun x =>
                     if x is Some r
                     then Some (encNonSPReg r)
                     else Some (false, #b"100")) _.
elim => //.
+ move => x y [<-]. by rewrite encNonSPRegK.
+ by move => y [<-]. Defined.

Definition optionalNonSPRegCodec (rex: bool) : Codec (option nonSPReg) :=
  always rex $ bitsCodec 3 ~~> optionalNonSPregCast.


Definition allReg: 16.-tuple reg
  := [tuple RAX:reg; RCX:reg; RDX:reg; RBX:reg; RSP:reg; RBP:reg; RSI:reg; RDI:reg;
      R8:reg; R9:reg; R10:reg; R11:reg; R12:reg; R13:reg; R14:reg; R15:reg
      (*RIP:reg*)].
Definition decReg (b: bool * BITS 3): reg := tnth allReg (toZp (joinmsb b)).
Definition encReg (r: reg) : bool * BITS 3 :=
  match r with
    | RSP => (false, #b"100")
    | R12 => (true, #b"100")
    | NonSPReg r => encNonSPReg r
  end.
Lemma encRegK : cancel encReg decReg. Proof. by case => //; case => //. Qed.
Canonical Structure RegEqMixin := CanEqMixin encRegK.
Canonical Structure RegEqType := Eval hnf in EqType _ RegEqMixin.
(*Instance RegEMB : EMB _ _ := Emb encRegK.
Coercion injReg := (@inj _ _ RegEMB).
*)

Definition regCast: CAST (bool * BITS 3) reg.
apply: MakeCast (fun x => decReg x) (fun x => Some (encReg x)) _.
move => x y [<-]; by rewrite encRegK. Defined.
Definition regCodec (rex: bool): Codec reg
  :=   always rex $ bitsCodec 3 ~~> regCast.


Definition mkOpSize b := if b then OpSize4 else OpSize1.
(*

Definition regCast : CAST (BITS 3) Reg.
apply: MakeCast (fun x => decReg x) (fun x => Some (encReg x)) _.
move => x y [<-]; by rewrite encRegK. Defined.
Definition regCodec   : Codec Reg   := bitsCodec 3 ~~> regCast.

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

Definition optionalNonSPregCast : CAST (BITS 3) (option NonSPReg).
apply: MakeCast (fun (x: BITS 3) => decNonSPReg x) (fun x =>
  if x is Some r then Some (encNonSPReg r) else Some #b"100") _.
elim => //.
+ move => x y [<-]. by rewrite encNonSPRegK.
+ by move => y [<-]. Defined.
Definition optionalNonSPRegCodec : Codec (option NonSPReg) :=
  bitsCodec 3 ~~> optionalNonSPregCast.

Definition nonSPregCast : CAST (BITS 3) NonSPReg.
apply: MakeCast (fun x => if decNonSPReg x is Some y then y else EAX)
                (fun y => Some (encNonSPReg y)) _.
move => x y [<-]. by rewrite encNonSPRegK. Defined.

Definition nonBPnonSPRegCodec : Codec NonSPReg :=
    #b"000" .$ always EAX
||| #b"001" .$ always ECX
||| #b"010" .$ always EDX
||| #b"011" .$ always EBX
||| #b"110" .$ always ESI
||| #b"111" .$ always EDI.

Definition nonSPRegCodec : Codec NonSPReg :=
    nonBPnonSPRegCodec
||| #b"101" .$ always EBP.

Definition sreg3Codec : Codec SegReg :=
    #b"000" .$ always ES
||| #b"001" .$ always CS
||| #b"010" .$ always SS
||| #b"011" .$ always DS
||| #b"100" .$ always FS
||| #b"101" .$ always GS.


Definition byteRegCast : CAST (BITS 3) BYTEReg.
apply: MakeCast (fun x => decBYTEReg x) (fun x => Some (encBYTEReg x)) _.
move => x y [<-]; by rewrite encBYTERegK. Defined.
Definition byteRegCodec : Codec BYTEReg := bitsCodec 3 ~~> byteRegCast.

Definition wordRegCast : CAST (BITS 3) WORDReg.
apply: MakeCast (fun x => decWORDReg x) (fun x => Some (encWORDReg x)) _.
move => x y [<-]; by rewrite encWORDRegK. Defined.
Definition wordRegCodec : Codec WORDReg := bitsCodec 3 ~~> wordRegCast.

Definition VRegCodec s : Codec (VReg s) :=
  match s with
  | OpSize1 => byteRegCodec
  | OpSize2 => wordRegCodec
  | OpSize4 => regCodec
  end.

Definition VWORDCodec s : Codec (VWORD s) :=
  match s with
  | OpSize1 => BYTECodec
  | OpSize2 => WORDCodec
  | OpSize4 => DWORDCodec
  end.

Definition scaleCast : CAST (BITS 2) Scale.
apply: MakeCast decScale (fun x => Some (encScale x)) _.
move => x y [<-]; by rewrite encScaleK. Defined.
Definition scaleCodec : Codec Scale := bitsCodec 2 ~~> scaleCast.

Definition conditionCast : CAST (BITS 3) Condition.
apply: MakeCast decCondition (fun x => Some (encCondition x)) _.
move => x y [<-]; by rewrite encConditionK. Defined.
Definition conditionCodec : Codec Condition := bitsCodec 3 ~~> conditionCast.

Hint Rewrite domConstSeq domSeq domCast domAlt domEmp domSym domAny : dom.

Lemma totalScale : total scaleCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalReg : total regCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totaloptionalNonSPReg : total optionalNonSPRegCodec. Proof. apply totalCast => //.
apply totalBITS. case => //. Qed.
Lemma totalOp : total opCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalShiftOp : total shiftOpCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalbyteReg : total byteRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totalwordReg : total wordRegCodec. Proof. apply totalCast => //. apply totalBITS. Qed.
Lemma totaldwordorbyteReg d : total (VRegCodec d).
Proof. destruct d. apply totalbyteReg. apply totalwordReg. apply totalReg. Qed.

Definition SIB := (Reg * option (NonSPReg * Scale))%type.

Definition SIBCast : CAST (Scale * option NonSPReg * Reg) SIB.
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

Definition SIBCodec : Codec SIB := scaleCodec $ optionalNonSPRegCodec $ regCodec ~~> SIBCast.

Lemma totalSIB : total SIBCodec.
Proof. rewrite /SIBCodec. apply totalCast. apply totalSeq. apply totalSeq.
apply totalScale. apply totaloptionalNonSPReg. apply totalReg.
rewrite /castIsTotal.  move => [r o]. destruct o => //. by destruct p.
Qed.

Definition dispOffsetSIBCast dword : CAST (SIB * DWORD) (RegMem dword).
apply: MakeCast (fun p => RegMemM dword (mkMemSpec (Some p.1) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some sib) offset) then Some(sib,offset) else None) _.
elim => //. elim => //. elim => //. move => [x y] z [x' y']. by move => [-> ->]. Defined.

Definition dispOffsetCast dword : CAST (NonSPReg * DWORD) (RegMem dword).
apply: (MakeCast (fun p => RegMemM dword (mkMemSpec (Some (nonSPReg p.1,None)) p.2))
  (fun rm => if rm is RegMemM (mkMemSpec (Some (nonSPReg base,None)) offset) then Some(base,offset) else None) _).
elim => //. elim => //. elim => //. move => [x y] z [x' y'].
case: x => // r. case: y => //. by move => [-> ->]. Defined.

Definition dispOffsetNoBaseCast dword : CAST DWORD (RegMem dword).
apply: MakeCast (fun offset => RegMemM dword (mkMemSpec None offset))
                (fun rm => if rm is RegMemM (mkMemSpec None offset)
                           then Some offset else None) _.
elim => //. elim => //. by elim => // ? ? [->]. Defined.

Definition RegMemCodec T (regOrOpcodeCodec : Codec T) dword : Codec (T * RegMem dword) :=
    #b"00" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ always #0 ~~> dispOffsetSIBCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (nonBPnonSPRegCodec $ always #0 ~~> dispOffsetCast dword)
||| #b"00" .$ regOrOpcodeCodec $ (#b"101" .$ DWORDCodec ~~> dispOffsetNoBaseCast dword)
||| #b"01" .$ regOrOpcodeCodec $ SIBRM .$ (SIBCodec $ shortDWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"01" .$ regOrOpcodeCodec $ (nonSPRegCodec $ shortDWORDCodec ~~> dispOffsetCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (SIBRM .$ SIBCodec $ DWORDCodec ~~> dispOffsetSIBCast dword)
||| #b"10" .$ regOrOpcodeCodec $ (nonSPRegCodec $ DWORDCodec ~~> dispOffsetCast dword)
||| #b"11" .$ regOrOpcodeCodec $ (VRegCodec dword ~~> unRegMemR dword).

(*
Lemma totalRegMemCodec T (c: Codec T) d : total c -> total (RegMemCodec c d).
Proof. move => tc. rewrite /total/RegMemCodec.
autorewrite with dom.
move => [x rm].
destruct rm.
(* Register *)
simpl. by rewrite totaldwordorbyteReg tc.
(* MemSpec *)
destruct ms.
case sib => [[base optix] |].
(* Has a SIB *)
+ case: optix => [[index sc] |].
  - simpl.
    rewrite /SIBCodec.
    case E: (offset == #0). rewrite (eqP E)/=. rewrite tc/=.
    destruct base; autorewrite with dom; simpl;
      by rewrite totalScale totaloptionalNonSPReg totalReg/=.
    destruct base; autorewrite with dom; simpl.
      rewrite totalScale totaloptionalNonSPReg totalDWORD totalReg tc /=.
      by rewrite !orbT !orbF.
    rewrite totalScale totaloptionalNonSPReg totalReg totalDWORD tc/=.
      by rewrite !orbT !orbF.
simpl.
simpl. rewrite totalDWORD/=. rewrite /SIBCodec.
autorewrite with dom. simpl.
case E: (offset == #0). simpl. by rewrite tc totalReg.
rewrite tc totalReg. simpl. by rewrite !orbT !orbF.
case E: (offset == #0). simpl. by rewrite tc totalDWORD.
(* Has no SIB  *)
by rewrite /= tc totalDWORD.
Qed.
*)

Definition RegMemOpCodec (op: BITS 3) dword :=
  RegMemCodec (Const op) dword ~~> sndUnitCast _.

Definition mkOpSize p b := if b then if p then OpSize2 else OpSize4 else OpSize1.

Definition unDstSrcRMR d : CAST (VReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d p.1 y
                              | RegMemM y => DstSrcRM d p.1 y end)
       (fun ds => match ds with DstSrcRR x y => Some (x,RegMemR _ y)
                              | DstSrcRM x y => Some (x,RegMemM _ y)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRR d : CAST (VReg d * RegMem d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.2 with RegMemR y => DstSrcRR d y p.1
                              | RegMemM y => DstSrcMR d y p.1 end)
       (fun ds => match ds with DstSrcRR x y => Some (y, RegMemR _ x)
                              | DstSrcMR x y => Some (y, RegMemM _ x)
                              | _ => None end) _).
by elim => // ? ? [? ?] [<-] <-. Defined.

Definition unDstSrcMRI d : CAST (RegMem d * VWORD d) (DstSrc d).
apply: (MakeCast
       (fun p => match p.1 with RegMemR y => (DstSrcRI d y p.2)
                             | RegMemM y => (DstSrcMI d y p.2) end)
       (fun ds => match ds with DstSrcRI x y => Some (RegMemR _ x, y)
                              | DstSrcMI x y => Some (RegMemM _ x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. by move => ? ? [<- ->]. Defined.

Definition unDstSrcRI d : CAST (VReg d * VWORD d) (DstSrc d).
apply: (MakeCast (fun p => DstSrcRI _ p.1 p.2)
       (fun ds => match ds with DstSrcRI x y => Some (x, y)
                              | _ => None end) _).
move => ds [rm c].
elim: ds => //. by move => ? ? [<- ->]. Defined.

(*---------------------------------------------------------------------------
    Casts for instructions
  ---------------------------------------------------------------------------*)
 *)

(* ** REX Prefix *)

Record REX := mkREX { W: bool;
                      R: bool;
                      X: bool;
                      B: bool }.

Definition rexPrefixCodec X (c : REX -> Codec X) : Codec X :=
  #x"4" .$ Cond (fun W =>
           Cond (fun R =>
           Cond (fun X =>
           Cond (fun B =>
                   c (mkREX W R X B)))))
   ||| c (mkREX false false false false). 

Example rexWCodec := rexPrefixCodec (fun rex => always (W rex)).
Example decREX1: dec rexWCodec (rev #x"48") = DecYes true [::]. done. Qed.
Example decREX2: dec rexWCodec (rev #x"47") = DecYes false [::]. done. Qed.
Example decREX3: dec rexWCodec (rev #x"F6") = DecYes false (rev #x"F6"). compute. done. Qed.

(* ** Size *)

(* if the lsb is 'false', we are playing on bytes.  Otherwise, we are
   on 32 or 64bits (depending on REX). Don't tell me about 16 bits: go
   back to the 70s grand'pa! *)

Definition opcodeWithSizeCodec X (opcode:BYTE) (c : bool -> Codec X) : Codec X :=
  droplsb opcode .$ Cond c.

Example mulOpCodec := opcodeWithSizeCodec #x"F6" (fun b => always b).
Example decOpSize1: dec mulOpCodec (rev #x"F6") = DecYes false [::]. done. Qed.
Example decOpSize2: dec mulOpCodec (rev #x"F7") = DecYes true [::]. done. Qed.

(** ** SIB byte *)

(** *** Scale *)

Definition allScales := [tuple S1; S2; S4; S8].
Definition decScale (b: BITS 2) := tnth allScales (toZp b).
Definition encScale r : BITS 2 :=
  match r with S1 => #b"00" | S2 => #b"01" | S4 => #b"10" | S8 => #b"11" end.
Lemma encScaleK : cancel encScale decScale. Proof. by case. Qed.
Canonical Structure ScaleEqMixin := CanEqMixin encScaleK.
Canonical Structure ScaleEqType := Eval hnf in EqType _ ScaleEqMixin.
(*Instance scaleEMB: EMB _ _ := Emb encScaleK.*)

Definition scaleCast : CAST (BITS 2) scale.
apply: MakeCast decScale (fun x => Some (encScale x)) _.
move => x y [<-]; by rewrite encScaleK.
Defined.

Definition scaleCodec : Codec scale := bitsCodec 2 ~~> scaleCast.

Example decScale1: dec scaleCodec (rev #b"00") = DecYes S1 [::]. done. Qed.
Example decScale2: dec scaleCodec (rev #b"01") = DecYes S2 [::]. done. Qed.
Example decScale3: dec scaleCodec (rev #b"10") = DecYes S4 [::]. done. Qed.
Example decScale4: dec scaleCodec (rev #b"11") = DecYes S8 [::]. done. Qed.

(** *** Index *)

Definition SIB := (reg * option (nonSPReg * scale))%type.

Definition SIBCast : CAST (scale * option nonSPReg * reg) SIB.
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

Definition SIBCodec (rex: REX) : Codec SIB
  := scaleCodec $ optionalNonSPRegCodec (X rex) $ regCodec (B rex) ~~> SIBCast.

Example rex32: REX := mkREX false false false false.
Example rexX: REX := mkREX false false true false.
Example rexB: REX := mkREX false false false true.
Example decSIB1: dec (SIBCodec rex32) (rev #x"20") = DecYes (RAX:reg, None) [::].
done. Qed.
Example decSIB2: dec (SIBCodec rex32) (rev #x"18") = DecYes (RAX:reg, Some (RBX, S1)) [::]. done. Qed.
Example decSIB3: dec (SIBCodec rex32) (rev #x"58") = DecYes (RAX:reg, Some (RBX, S2)) [::]. done. Qed.
Example decSIB4: dec (SIBCodec rexX) (rev #x"20") = DecYes (RAX:reg, None) [::]. done. Qed.
Example decSIB5: dec (SIBCodec rexX) (rev #x"18") = DecYes (RAX:reg, Some (R11, S1)) [::]. done. Qed.
Example decSIB6: dec (SIBCodec rexX) (rev #x"58") = DecYes (RAX:reg, Some (R11 , S2)) [::]. done. Qed.
Example decSIB7: dec (SIBCodec rexB) (rev #x"20") = DecYes (R8:reg, None) [::]. done. Qed.
Example decSIB8: dec (SIBCodec rexB) (rev #x"18") = DecYes (R8:reg, Some (RBX, S1)) [::]. done. Qed.
Example decSIB9: dec (SIBCodec rexB) (rev #x"58") = DecYes (R8:reg, Some (RBX , S2)) [::]. done. Qed.
(* TODO: do we actually need offset? Test it *) 

(* ** ModRM byte *)

Definition dispOffsetCast dword : CAST (nonSPReg * DWORD) (regmem dword).
  apply: MakeCast
           (fun p => RegMemM _ (mkMemSpec (Some (NonSPReg p.1), None) p.2))
           (fun rm =>
              if rm is RegMemM (mkMemSpec (Some (NonSPReg base), None) offset) then
                Some (base, offset)
              else None) _.
  (* TODO: fix proof *)
  case=> //; case=> //; case=> //; case=> //; case=> //; move=> r. case=> //. move=> ? ? [<-] //=.
Defined.

Definition dispOffsetSIBCast dword : CAST (SIB * DWORD) (regmem dword).
  apply: MakeCast
           (fun p => RegMemM _ (mkMemSpec (Some p.1.1, p.1.2) p.2))
           (fun rm => if rm is RegMemM (mkMemSpec (Some r, sib) offset) then
                        Some((r, sib),offset)
                      else None) _.
  elim => //. elim => //. elim => //. elim=> //. move=> ? ? ? ? [<-] //=. 
Defined.

Definition dispOffsetNoBaseCast dword : CAST DWORD (regmem dword).
apply: MakeCast (fun offset => RegMemM dword (RIP offset))
                (fun rm => if rm is RegMemM (RIP offset)
                           then Some offset else None) _.
elim => //; elim => //. move=> ? ? [->] //.
Defined.


(* *** Mod = 00: Indirect addressing *)

Definition Mod00RMCodec rex dword : Codec (regmem dword)
  := (* Any register but BP and SP: *)
      nonBPnonSPRegCodec (R rex) $ always #0 ~~> dispOffsetCast dword
 ||| (* SIB: *)
     #b"100" .$ (SIBCodec rex $ always #0 ~~> dispOffsetSIBCast dword)              
 ||| (* Offset: *)
     #b"101" .$ DWORDCodec ~~> dispOffsetNoBaseCast dword.   

Local Open Scope memspec_scope.

Conjecture repr0: #0 = Tuple (nseq_tupleP 32 false).
(* Registers: *)
Example decMod00RM1: dec (Mod00RMCodec rex32 OpSize4) (rev #b"000") = DecYes (RegMemM _ [ RAX ]) [::]. compute. rewrite -repr0. done. Qed.
Example decMod00RM2: dec (Mod00RMCodec rex32 OpSize4) (rev #b"001") = DecYes (RegMemM _ [ RCX ]) [::]. compute. rewrite -repr0. done. Qed.
(* Offset: *)
Definition decMod00RM3: dec (Mod00RMCodec rex32 OpSize4) (rev #b"10100000000000000000000000000000000") = DecYes (RegMemM _ [ rel #x"00000000"]) [::]. compute. admit. Qed.
(* SIB: *)
Definition decMod00RM4: dec (Mod00RMCodec rex32 OpSize4) (rev #b("100"++ "00" ++ "000" ++ "001")) = DecYes (RegMemM _ [ RCX + RAX + #0 ]) [::]. compute. done. Qed.
Definition decMod00RM5: dec (Mod00RMCodec rex32 OpSize4) (rev #b("100" ++ "00" ++ "100" ++ "100")) = DecYes (RegMemM _ [ RSP ]) [::]. compute. rewrite -repr0. done. Qed.
(* TODO: more examples *)

Local Close Scope memspec_scope.


(* *** Mod = 01: +disp8 addressing *)

Definition Mod01RMCodec rex dword : Codec (regmem dword)
  := (* Any register but RSP: *)
      nonSPRegCodec (R rex) $ shortDWORDCodec ~~> dispOffsetCast dword
 ||| (* SIB: *)
     #b"100" .$ (SIBCodec rex $ shortDWORDCodec ~~> dispOffsetSIBCast dword).

(* TODO: I don't think the syntax allows us to write 8bits offsets. It wants DWORDs. *)

Local Open Scope memspec_scope.

(* Registers: *)
(*
Example decMod01RM1: dec (Mod01RMCodec rex32 OpSize4) (rev #b("001" ++ "0001" ++ "0010")) = DecYes (RegMemM _ [ RCX + #x"12" ]) [::]. compute. 
*)
(* TODO: more examples *)

Local Close Scope memspec_scope.

(* *** Mod = 10: +disp32 addressing *)

Definition Mod10RMCodec rex dword : Codec (regmem dword)
  := (* Any register but SP: *)
      nonSPRegCodec (R rex) $ DWORDCodec ~~> dispOffsetCast dword
 ||| (* SIB: *)
     #b"100" .$ (SIBCodec rex $ DWORDCodec ~~> dispOffsetSIBCast dword).

Local Open Scope memspec_scope.

(* Registers: *)
(*
 Example decMod10RM1: dec (Mod01RMCodec rex32 OpSize4) (rev #b("001" ++ "0111" ++ "1000" ++ "0101" ++ "0110" ++ "0100" ++ "0011" ++ "0001" ++ "0010")) = DecYes (RegMemM _ [ RCX + #x"78563412" ]) [::]. compute. 
 *)

Local Close Scope memspec_scope.


Definition byteRegCast : CAST (BITS 3) BYTELReg.
  admit.
  (*
apply: MakeCast (fun x => decBYTELReg x) (fun x => Some (encBYTELReg x)) _.
move => x y [<-]; by rewrite encBYTERegK. *)
Defined.
Definition byteRegCodec : Codec BYTELReg := bitsCodec 3 ~~> byteRegCast.

Definition decWORDReg (b: bool * BITS 3) := mkWordReg (decReg b).
Definition encWORDReg wr := let: mkWordReg r := wr in encReg r. 
Lemma encWORDRegK : cancel encWORDReg decWORDReg.
Proof. case => r/=. rewrite /decWORDReg. by rewrite encRegK. Qed. 

Definition wordRegCast : CAST (bool * BITS 3) WORDReg.
apply: MakeCast (fun x => decWORDReg x) (fun x => Some (encWORDReg x)) _.
move => x y [<-]; by rewrite encWORDRegK. Defined.
Definition wordRegCodec (rex: bool): Codec WORDReg :=
  always rex $ bitsCodec 3 ~~> wordRegCast.

Definition admitted: forall A, A. admit. Defined.

Definition VRegCodec (rex: bool) s : Codec (vreg s) :=
  match s with
    | OpSize1 => admitted _ (*byteRegCodec*)
    | OpSize2 => wordRegCodec rex
    | OpSize4 => regCodec rex
  end.


Definition Mod11RMCodec (rex: REX) dword : Codec (regmem dword)
  := regCodec (W rex).
  (* Any register: *)
    (* VRegCodec dword ~~> unRegMemR dword. *)
    (* 32-bits register: *)



Definition ModRMCodec  T (regOrOpcodeCodec : Codec T) rex dword : Codec (T * regmem dword)
  := #b"00" .$ regOrOpcodeCodec $ Mod00RMCodec rex dword
 ||| #b"01" .$ regOrOpcodeCodec $ Mod01RMCodec rex dword
 ||| #b"10" .$ regOrOpcodeCodec $ Mod10RMCodec rex dword
 ||| #b"11" .$ regOrOpcodeCodec $ Mod11RMCodec rex dword.

Definition ModRMOpCodec (op: BITS 3)(rex: REX) dword: Codec (regmem dword) :=
  ModRMCodec (Const op) rex dword ~~> sndUnitCast _.


(*

Definition prefAndOpSizeToBool (w: bool) (os: OpSize) :=  
  match os, w with
  | OpSize4, false => Some true
  | OpSize2, true => Some true
  | OpSize1, _ => Some false  
  | _, _ => None
  end.

Definition opSizePrefixCodec X (c : bool -> Codec X) : Codec X :=
    #x"66" .$ (c true)
||| c false.

Definition isCMC : CAST unit Instr.
apply: MakeCast (fun _ => CMC) (fun i => if i is CMC then Some tt else None) _; by elim; elim.
Defined.

Definition isCLC : CAST unit Instr.
apply: MakeCast (fun _ => CLC) (fun i => if i is CLC then Some tt else None) _; by elim; elim.
Defined.

Definition isSTC : CAST unit Instr.
apply: MakeCast (fun _ => STC) (fun i => if i is STC then Some tt else None) _; by elim; elim.
Defined.


Definition isENCLU : CAST unit Instr.
apply: MakeCast (fun _ => ENCLU) (fun i => if i is ENCLU then Some tt else None) _; by elim; elim.
Defined.

Definition isENCLS : CAST unit Instr.
apply: MakeCast (fun _ => ENCLS) (fun i => if i is ENCLS then Some tt else None) _; by elim; elim.
Defined.

Definition TgtCodec : Codec Tgt := DWORDCodec ~~> unTgt.
Definition ShortTgtCodec : Codec Tgt := shortDWORDCodec ~~> unTgt.

Definition VAXCodec os : Codec (VReg os) :=
match os return Codec (VReg os) with
| OpSize1 => always AL
| OpSize2 => always AX
| OpSize4 => always (EAX:Reg)
end.


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
    JCC instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unJCC : CAST (Condition*bool*Tgt) Instr.
apply: MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _.
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.

Definition JCCCodec :=
    #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ TgtCodec ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec  ~~> unJCC.


(*---------------------------------------------------------------------------
    PUSH instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unPUSH : CAST Src Instr.
apply: MakeCast PUSH (fun i => if i is PUSH s then Some s else None) _.
by elim => // ? ? [->]. Defined.

Definition unPUSHSegR : CAST SegReg Instr.
apply: MakeCast PUSHSegR (fun i => if i is PUSHSegR r then Some r else None) _.
by elim => // ? ? [->]. Defined.

Definition PUSHCodec := 
    #x"68" .$ DWORDCodec ~~> unSrcI ~~> unPUSH
||| #x"6A" .$ shortDWORDCodec ~~> unSrcI ~~> unPUSH
||| #b"01010" .$ regCodec ~~> unSrcR ~~> unPUSH
||| #x"FF" .$ RegMemOpCodec #6 _ ~~> unSrcRM ~~> unPUSH
||| #x"0E" .$ always CS ~~> unPUSHSegR
||| #x"16" .$ always SS ~~> unPUSHSegR
||| #x"1E" .$ always DS ~~> unPUSHSegR
||| #x"06" .$ always ES ~~> unPUSHSegR
||| #x"0F" .$ #x"A0" .$ always FS ~~> unPUSHSegR
||| #x"0F" .$ #x"A8" .$ always GS ~~> unPUSHSegR.

(*---------------------------------------------------------------------------
    POP instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unPOP : CAST (RegMem OpSize4) Instr.
apply: MakeCast POP (fun i => if i is POP d then Some d else None) _.
elim => //. by move => d rm [->]. Defined.

Definition unPOPSegR : CAST SegReg Instr.
apply: MakeCast POPSegR (fun i => if i is POPSegR r then Some r else None) _.
by elim => // ? ? [->]. Defined.

Definition POPCodec :=
    #x"8F" .$ RegMemOpCodec #0 _ ~~> unPOP
||| #b"01011" .$ regCodec ~~> unRegMemR OpSize4 ~~> unPOP
||| #x"17" .$ always SS ~~> unPOPSegR
||| #x"1F" .$ always DS ~~> unPOPSegR
||| #x"07" .$ always ES ~~> unPOPSegR
||| #x"0F" .$ #x"A1" .$ always FS ~~> unPOPSegR
||| #x"0F" .$ #x"A9" .$ always GS ~~> unPOPSegR.

(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)
Definition unMOVRMSeg : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVRMSeg p.2 p.1) (fun i => if i is MOVRMSeg x y then Some(y,x) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOVSegRM : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVSegRM p.1 p.2) (fun i => if i is MOVSegRM x y then Some(x,y) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOV w d : CAST (DstSrc (mkOpSize w d)) Instr.
apply (MakeCast (MOVOP _) (fun i => if i is MOVOP _ d then tryEqOpSize _ d else None)). 
by elim:w; elim:d; elim => //; elim => //; move => ? src [->]. 
Defined. 

Definition MOVCodec :=
  opSizePrefixCodec (fun w =>
      (* MOV r/m8, r8 | MOV r/m16, r16 | MOV r/m32, r32 *)
      opcodeWithSizeCodec #x"88" (fun d =>
        RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _ ~~> unMOV w d)
      (* MOV r8, r/m8 | MOV r16, r/m16 | MOV r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"8A" (fun d =>   
        RegMemCodec (VRegCodec _) _  ~~> unDstSrcRMR _ ~~> unMOV w d)
      (* MOV r/m8, imm8 | MOV r/m16, imm16 | MOV r/m32, imm32 *)
  ||| opcodeWithSizeCodec #x"C6" (fun d =>
        RegMemOpCodec #0 _ $ VWORDCodec _ ~~> unDstSrcMRI _ ~~> unMOV w d)
      (* MOV r8, imm8 | MOV r16, imm16 | MOV r32, imm32 *)
  ||| #x"B" .$ Cond (fun d => 
        VRegCodec _ $ VWORDCodec _ ~~> unDstSrcRI _ ~~> unMOV w d)
  )
  (* MOV r/m16, Sreg *)
||| #x"8C" .$ RegMemCodec sreg3Codec _ ~~> unMOVRMSeg

  (* MOV Sreg, r/m16 *)
||| #x"8E" .$ RegMemCodec sreg3Codec _ ~~> unMOVSegRM.

(*---------------------------------------------------------------------------
    MOVX instruction
  ---------------------------------------------------------------------------*)
(*
Definition unMOVZX s : CAST (Reg * RegMem s) Instr.
  apply (MakeCast (fun v => MOVX false _ v.1 v.2)) (RegMemR _ v.2))).
  (fun i => if i is TESTOP os x (RegImmR y) then prefAndOpSizeToBool1 w y x else None) _).
  elim:w; elim => //; elim => //; move => r; elim => // s; move => q H; by inversion H. 
apply: MakeCast (fun p => MOVX false OpSize4 p.1 p.2) (fun i => if i is MOVX false OpSize4 x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? ? [<-]. Defined.

Definition unMOVSX : CAST (Reg * RegMem true) Instr.
apply: MakeCast (fun p => MOVX true true p.1 p.2) (fun i => if i is MOVX true true x y then Some(x,y) else None) _.
elim => //. elim => //. elim => //. by move => ? ? [? ?] [-> ->]. Defined.

Definition MOVXCodec :=
    opSizePrefixCodec (fun w => #x"0F" .$ VRegMemRegCodec _ #x"B6" ~~> unMOVZX w)
||| #x"0F" .$ #x"B7" .$ RegMemCodec regCodec true ~~> unMOVZX
||| #x"0F" .$ #x"BE" .$ RegMemCodec regCodec false ~~> unMOVSXB
||| #x"0F" .$ #x"BF" .$ RegMemCodec regCodec true ~~> unMOVSX.
*)

(*---------------------------------------------------------------------------
    BT, BTC, BTR, BTS instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
Definition unBITOPR : CAST (BitOp * (Reg * RegMem OpSize4)) Instr.
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
    #x"0F" .$ BITOPPREF .$ bitOpCodec $ BITOPSUFF .$ (RegMemCodec regCodec _) ~~> unBITOPR
||| #x"0F" .$ #x"BA" .$ RegMemCodec (#b"1" .$ bitOpCodec) _ $ BYTECodec ~~> unBITOPI.


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
  opSizePrefixCodec (fun w => 
    (
      opcodeWithSizeCodec #x"C0" (fun d => 
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D0" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D2" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT _)
    )
  ).

(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
Definition unBOP s : CAST (BinOp * DstSrc s) Instr.
apply: (MakeCast (fun p => BOP _ p.1 p.2))
                 (fun i => if i is BOP s1 op v 
                  then tryEqOpSize (F:=fun s => (BinOp*DstSrc s)%type) s (op,v) else None) _.  elim:s; elim => //; elim => //; move => ? src [? ?]; by move => [-> ->]. 
Defined.

Definition shortVWORDEmb w : CAST BYTE (VWORD (if w then OpSize2 else OpSize4)).
destruct w. 
apply: MakeCast (@signExtend 8 7) (@signTruncate 8 7) _.
- move => d b/= H. by apply signTruncateK. 
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
- move => d b/= H. by apply signTruncateK. 
Defined.

Definition shortVWORDCodec w: Codec _ :=
  BYTECodec ~~> shortVWORDEmb w.

Definition BINOPCodec :=
    opSizePrefixCodec (fun w => 
      (* OP AL, imm8 | OP AX, imm16 | OP EAX, imm32 *)
    #b"00" .$ opCodec $ #b"100" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"101" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, r8 | OP r/m16, r16 | OP r/m32, r32 *)
||| #b"00" .$ opCodec $ #b"010" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"011" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w true)

    (* OP r8, r/m8 | OP r16, r/m16 | OP r32, r/m32 *)
||| #b"00" .$ opCodec $ #b"000" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"001" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, imm8 | OP r/m16, imm16 | OP r/m32, imm32 *)
||| opcodeWithSizeCodec #x"80" (fun d => RegMemCodec opCodec _ $ VWORDCodec _
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP (mkOpSize w d))

    (* OP r/m16, imm8 | OP r/m32, imm8 (sign-extended) *)
||| #x"83" .$ (RegMemCodec opCodec _ $ shortVWORDCodec w) 
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP _ 

    )
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
  opSizePrefixCodec (fun w => 
    opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec #0 _ ~~> unINC (mkOpSize w d))

||| opcodeWithSizeCodec #x"FE" (fun d =>
    RegMemOpCodec #1 _ ~~> unDEC (mkOpSize w d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec #2 _ ~~> unNOT (mkOpSize w d))

||| opcodeWithSizeCodec #x"F6" (fun d =>
    RegMemOpCodec #3 _ ~~> unNEG (mkOpSize w d))

||| INCPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unINC (mkOpSize w false)
||| DECPREF .$ VRegCodec _ ~~> unRegMemR _ ~~> unDEC (mkOpSize w false)
  ).


(*---------------------------------------------------------------------------
    IN/OUT instructions
  ---------------------------------------------------------------------------*)
Definition unINI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => INOP (mkOpSize w p.1) (PortI p.2)) 
       (fun i => if i is INOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unOUTI (w:bool) : CAST (bool*BYTE) Instr.
apply: (MakeCast (fun p => OUTOP (mkOpSize w p.1) (PortI p.2)) (fun i => if i is OUTOP os (PortI p) then if prefAndOpSizeToBool w os is Some d then Some(d,p) else None else None) _).
elim: w; elim => //; elim => //; elim => // => ? [? ?] H; by inversion H. Defined.

Definition unINR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => INOP (mkOpSize w p) PortDX) 
  (fun i => if i is INOP os PortDX then prefAndOpSizeToBool w os else None) _.
elim: w; elim => //; elim => //; elim => // => ? H; by inversion H. 
Defined. 

Definition unOUTR (w:bool) : CAST bool Instr.
apply: MakeCast (fun p => OUTOP (mkOpSize w p) PortDX) 
  (fun i => if i is OUTOP os PortDX then prefAndOpSizeToBool w os else None) _.
elim: w; elim => //; elim => //; elim => // => ? H; by inversion H. 
Defined. 

Definition INOUTCodec :=
    opSizePrefixCodec (fun w => droplsb #x"E4" .$ Any $ BYTECodec ~~> unINI w)
||| opSizePrefixCodec (fun w => droplsb #x"E6" .$ Any $ BYTECodec ~~> unOUTI w)
||| opSizePrefixCodec (fun w => droplsb #x"EC" .$ Any ~~> unINR w)
||| opSizePrefixCodec (fun w => droplsb #x"EE" .$ Any ~~> unOUTR w).

(*---------------------------------------------------------------------------
    MUL and IMUL instructions
  ---------------------------------------------------------------------------*)
Definition unIMUL : CAST (Reg * RegMem OpSize4) Instr.
apply: (MakeCast (fun p => IMUL p.1 p.2)
                 (fun i => if i is IMUL dst src then Some (dst,src) else None) _).
elim => //. by move => dst src [dst' src'] [<-] ->.  Defined.

Definition unMUL s : CAST (RegMem s) Instr.
apply: (MakeCast (@MUL s)
                 (fun i => if i is MUL s1 v 
                  then tryEqOpSize s v else None) _).  
elim: s; elim => //; elim => //; move => r q H; by inversion H.  
Defined.

Definition MULCodec :=
    (* IMUL r32, r/m32 *)
    #x"0F" .$ #x"AF" .$ RegMemCodec regCodec _ ~~> unIMUL

    (* MUL r/m8 | MUL r/m16 | MUL r/m32 *)
||| opSizePrefixCodec (fun w => 
    opcodeWithSizeCodec #x"F6" (fun d =>  
    RegMemOpCodec #4 _ ~~> unMUL (mkOpSize w d))).

(*---------------------------------------------------------------------------
    LEA instruction 
  ---------------------------------------------------------------------------*)
Definition unLEA : CAST (Reg * RegMem OpSize4) Instr.
apply: MakeCast (fun p => LEA p.1 p.2) (fun i => if i is LEA x y then Some(x,y) else None) _.
by elim => // ? ? [? ?] [-> ->]. Defined.

Definition LEACodec :=
  #x"8D" .$ RegMemCodec regCodec _ ~~> unLEA.

(*---------------------------------------------------------------------------
    XCHG instruction 
  ---------------------------------------------------------------------------*)
Definition unXCHG s : CAST (VReg s * RegMem s) Instr. 
Proof. 
  apply: MakeCast (fun p => XCHG s p.1 p.2) 
  (fun i => if i is XCHG s1 x y 
            then tryEqOpSize (F:=fun s => (VReg s * RegMem s)%type) s (x,y) else None) _.  
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined. 

Definition XCHGCodec :=
    opSizePrefixCodec (fun w => 
      (* XCHG AX, r16 | XCHG EAX, r32 *)
      #b"10010" .$ VAXCodec _ $ (VRegCodec _ ~~> unRegMemR _) ~~> unXCHG (mkOpSize w true)
      (* XCHG r8, r/m8 | XCHG r16, r/m16 | XCHG r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"86" (fun d =>
        RegMemCodec (VRegCodec _) _ ~~> unXCHG (mkOpSize w d))
  ).

*)

(*---------------------------------------------------------------------------
    HLT
  ---------------------------------------------------------------------------*)

Definition isHLT : CAST unit Instr.
  apply: MakeCast (fun _ => HLT)
                  (fun i => if i is HLT then Some tt else None) _.
  by case; case.
Defined.

Definition HLTCodec: Codec Instr
  := #x"F4" ~~> isHLT.

Example decHLT: dec HLTCodec (rev #x"F4") = DecYes HLT [::]. done. Qed.


(*---------------------------------------------------------------------------
    ADC/ADD/SUB/SBB/OR/AND/XOR/CMP instructions
  ---------------------------------------------------------------------------*)
(*
Definition unBOP s : CAST (BinOp * DstSrc s) Instr.
apply: (MakeCast (fun p => BOP _ p.1 p.2))
                 (fun i => if i is BOP s1 op v 
                  then tryEqOpSize (F:=fun s => (BinOp*DstSrc s)%type) s (op,v) else None) _.  elim:s; elim => //; elim => //; move => ? src [? ?]; by move => [-> ->]. 
Defined.

Definition shortVWORDEmb w : CAST BYTE (VWORD (if w then OpSize2 else OpSize4)).
destruct w. 
apply: MakeCast (@signExtend 8 7) (@signTruncate 8 7) _.
- move => d b/= H. by apply signTruncateK. 
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
- move => d b/= H. by apply signTruncateK. 
Defined.

Definition shortVWORDCodec w: Codec _ :=
  BYTECodec ~~> shortVWORDEmb w.
 *)

Definition BINOPCodec: Codec Instr. admit. Defined.
(*
    opSizePrefixCodec (fun w => 
      (* OP AL, imm8 | OP AX, imm16 | OP EAX, imm32 *)
    #b"00" .$ opCodec $ #b"100" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"101" .$ 
      (VAXCodec _ $ VWORDCodec _ ~~> unDstSrcRI _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, r8 | OP r/m16, r16 | OP r/m32, r32 *)
||| #b"00" .$ opCodec $ #b"010" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"011" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcRMR _) ~~> unBOP (mkOpSize w true)

    (* OP r8, r/m8 | OP r16, r/m16 | OP r32, r/m32 *)
||| #b"00" .$ opCodec $ #b"000" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w false)
||| #b"00" .$ opCodec $ #b"001" .$ 
      (RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _) ~~> unBOP (mkOpSize w true)

    (* OP r/m8, imm8 | OP r/m16, imm16 | OP r/m32, imm32 *)
||| opcodeWithSizeCodec #x"80" (fun d => RegMemCodec opCodec _ $ VWORDCodec _
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP (mkOpSize w d))

    (* OP r/m16, imm8 | OP r/m32, imm8 (sign-extended) *)
||| #x"83" .$ (RegMemCodec opCodec _ $ shortVWORDCodec w) 
    ~~> pairAssocCastOp _ _ _ ~~> pairOfCasts (idCast _) (unDstSrcMRI _) ~~> unBOP _ 

    )
.
*)

(*---------------------------------------------------------------------------
    JMP instruction
    @TODO: 16-bit variants, far jumps
  ---------------------------------------------------------------------------*)
(*
Definition unJMP : CAST JmpTgt Instr.
apply: MakeCast JMPrel (fun i => if i is JMPrel t then Some t else None) _.
by elim => // ? ? [->]. 
Defined.
*)
Definition JMPCodec: Codec Instr. admit. Defined.
(*                                  
    #x"EB" .$ ShortTgtCodec ~~> unJmpTgtI ~~> unJMP
||| #x"E9" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unJMP
||| #x"FF" .$ RegMemOpCodec #4 OpSize4 ~~> unJmpTgtRM ~~> unJMP.
*)

(*---------------------------------------------------------------------------
    CALL instruction
    @TODO: 16-bit variants, far calls
  ---------------------------------------------------------------------------*)

(*
Definition unCALL : CAST JmpTgt Instr.
apply: MakeCast CALLrel (fun i => if i is CALLrel t then Some t else None) _.
by elim => // ? ? [->]. 
Defined.
 *)

Definition CALLCodec: Codec Instr. admit. Defined.
(*                            
    #x"E8" .$ DWORDCodec ~~> unTgt ~~> unJmpTgtI ~~> unCALL
||| #x"FF" .$ RegMemOpCodec #2 OpSize4 ~~> unJmpTgtRM ~~> unCALL.
*)

(*---------------------------------------------------------------------------
    RET instruction (near)
  ---------------------------------------------------------------------------*)
(*
Definition unRET : CAST WORD Instr.
apply: MakeCast RETOP (fun i => if i is RETOP w then Some w else None) _.
by elim => // ? ? [->]. 
Defined.
*)

Definition RETCodec: Codec Instr. admit. Defined.
(*
    #x"C3" .$ always #0 ~~> unRET
||| #x"C2" .$ WORDCodec ~~> unRET.
*)

(*---------------------------------------------------------------------------
    TEST instruction
  ---------------------------------------------------------------------------*)

(*
Definition tryEqOpSize F (s1 s2: OpSize): F s1 -> option (F s2) :=
  match s1, s2 with
  | OpSize1, OpSize1 => fun x => Some x
  | OpSize2, OpSize2 => fun x => Some x
  | OpSize4, OpSize4 => fun x => Some x
  | _, _ => fun x => None
  end. 

Definition unTEST s : CAST (RegMem s * RegImm s) Instr.
apply (MakeCast (fun p => TESTOP s p.1 p.2)
                (fun i => if i is TESTOP s1 x d
  then tryEqOpSize (F:= fun s=> (RegMem s * RegImm s)%type) s (x,d) else None)). 
elim:s; elim => //; elim => //; move => ? src [? ?]; case src => // ?; by move => [-> ->].
Defined.
 *)

Definition TESTCodec: Codec Instr. admit. Defined.
(*
  opSizePrefixCodec (fun w =>
    (* Short form for TEST AL/AX/EAX, imm8/imm16/imm32 *)
        opcodeWithSizeCodec #x"A8" (fun d => 
        (VAXCodec (mkOpSize w d) ~~> unRegMemR _) $ (VWORDCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, imm8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| opcodeWithSizeCodec #x"F6" (fun d =>
        RegMemOpCodec #0 (mkOpSize w d) $ (VWORDCodec _ ~~> unRegImmI _) ~~> unTEST _)
    (* TEST r/m8, r8 | TEST r/m16, r16 | TEST r/m32, r32 *)
    ||| opcodeWithSizeCodec #x"84" (fun d =>
        RegMemCodec (VRegCodec _ ~~> unRegImmR _) _ ~~> swapPairCast _ _ ~~> unTEST (mkOpSize w d))
    ).
*)


(*---------------------------------------------------------------------------
    MOV instruction
  ---------------------------------------------------------------------------*)

(*
Definition unMOVRMSeg : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVRMSeg p.2 p.1) (fun i => if i is MOVRMSeg x y then Some(y,x) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOVSegRM : CAST (SegReg * RegMem OpSize2) Instr.
apply: (MakeCast (fun p => MOVSegRM p.1 p.2) (fun i => if i is MOVSegRM x y then Some(x,y) else None) _).
by elim => // ? ? [? ?] [-> ->]. 
Defined.

Definition unMOV w d : CAST (DstSrc (mkOpSize w d)) Instr.
apply (MakeCast (MOVOP _) (fun i => if i is MOVOP _ d then tryEqOpSize _ d else None)). 
by elim:w; elim:d; elim => //; elim => //; move => ? src [->]. 
Defined. 
*)
  
Definition MOVCodec: Codec Instr. admit. Defined.
  (*
  opSizePrefixCodec (fun w =>
      (* MOV r/m8, r8 | MOV r/m16, r16 | MOV r/m32, r32 *)
      opcodeWithSizeCodec #x"88" (fun d =>
        RegMemCodec (VRegCodec _) _ ~~> unDstSrcMRR _ ~~> unMOV w d)
      (* MOV r8, r/m8 | MOV r16, r/m16 | MOV r32, r/m32 *)
  ||| opcodeWithSizeCodec #x"8A" (fun d =>   
        RegMemCodec (VRegCodec _) _  ~~> unDstSrcRMR _ ~~> unMOV w d)
      (* MOV r/m8, imm8 | MOV r/m16, imm16 | MOV r/m32, imm32 *)
  ||| opcodeWithSizeCodec #x"C6" (fun d =>
        RegMemOpCodec #0 _ $ VWORDCodec _ ~~> unDstSrcMRI _ ~~> unMOV w d)
      (* MOV r8, imm8 | MOV r16, imm16 | MOV r32, imm32 *)
  ||| #x"B" .$ Cond (fun d => 
        VRegCodec _ $ VWORDCodec _ ~~> unDstSrcRI _ ~~> unMOV w d)
  )
  (* MOV r/m16, Sreg *)
||| #x"8C" .$ RegMemCodec sreg3Codec _ ~~> unMOVRMSeg

  (* MOV Sreg, r/m16 *)
||| #x"8E" .$ RegMemCodec sreg3Codec _ ~~> unMOVSegRM.
*)

(*---------------------------------------------------------------------------
    SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR instructions
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)

(*
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
*)

Definition SHIFTCodec: Codec Instr. admit. Defined.
(*
  opSizePrefixCodec (fun w => 
    (
      opcodeWithSizeCodec #x"C0" (fun d => 
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (BYTECodec ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D0" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (always #1 ~~> unShiftCountI) ~~> unSHIFT _) |||
      opcodeWithSizeCodec #x"D2" (fun d =>
        RegMemCodec shiftOpCodec (mkOpSize w d) $ (Emp ~~> unShiftCountCL) ~~> unSHIFT _)
    )
  ).
*)

(*---------------------------------------------------------------------------
    JCC instruction
    @TODO: 16-bit variants
  ---------------------------------------------------------------------------*)
(*
Definition unJCC : CAST (Condition*bool*Tgt) Instr.
apply: MakeCast (fun p => let: (c,d,t) := p in JCCrel c (negb d) t)
                (fun i => if i is JCCrel c d t then Some(c,negb d,t) else None) _.
Proof. elim => //. move => cc cv tgt [[cc' cv'] tgt']. move => [-> <- ->].
by rewrite negbK. Defined.
 *)

Definition JCCCodec: Codec Instr. admit. Defined.
(*
    #x"0F" .$ JCC32PREF .$ conditionCodec $ Any $ TgtCodec ~~> unJCC
||| JCC8PREF .$ conditionCodec $ Any $ ShortTgtCodec  ~~> unJCC.
 *)

(*---------------------------------------------------------------------------
    MUL instructions
  ---------------------------------------------------------------------------*)

(* TODO: remove *)
Definition tryEqOpSize F (s1 s2: opsize): F s1 -> option (F s2) :=
  match s1, s2 with
  | OpSize1, OpSize1 => fun x => Some x
  | OpSize2, OpSize2 => fun x => Some x
  | OpSize4, OpSize4 => fun x => Some x
  | _, _ => fun x => None
  end. 


Definition unMUL s : CAST (regmem s) Instr.
apply: (MakeCast (@MUL s)
                 (fun i => if i is MUL s1 v 
                  then tryEqOpSize s v else None) _).  
elim: s; elim => //; elim => //; move => r q H; by inversion H.  
Defined.

  
Definition MULCodec (rex: REX): Codec Instr
  := (* MUL r/m8 | MUL r/m32 | MUL r/m64 *)
    opcodeWithSizeCodec #x"F6" (fun d =>  
    ModRMOpCodec #4 rex (mkOpSize d) ~~> unMUL (mkOpSize d)).

(*---------------------------------------------------------------------------
    IMUL instructions
  ---------------------------------------------------------------------------*)

                                                 (*
Definition unIMUL : CAST (Reg * RegMem OpSize4) Instr.
apply: (MakeCast (fun p => IMUL p.1 p.2)
                 (fun i => if i is IMUL dst src then Some (dst,src) else None) _).
elim => //. by move => dst src [dst' src'] [<-] ->.  Defined.
*)

Definition IMULCodec: Codec Instr. admit. Defined.
(*
    (* IMUL r32, r/m32 *)
    #x"0F" .$ #x"AF" .$ RegMemCodec regCodec _ ~~> unIMUL

    (* MUL r/m8 | MUL r/m16 | MUL r/m32 *)
 *)

(*---------------------------------------------------------------------------
    All instructions
  ---------------------------------------------------------------------------*)


Definition InstrCodec : Codec Instr :=
  HLTCodec
    ||| BINOPCodec
    ||| JMPCodec
    ||| CALLCodec
    ||| RETCodec
    ||| TESTCodec
    ||| MOVCodec
    ||| SHIFTCodec
    ||| JCCCodec
    ||| MULCodec
    ||| IMULCodec.

