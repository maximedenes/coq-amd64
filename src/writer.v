(*===========================================================================
    Syntax for writers, with instances for BYTE and DWORD
  ===========================================================================*)
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.finfun Ssreflect.fintype Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.tuple.
Require Import bitsrep bitsops cursor monad monadinst cstring.
Require Import Coq.Logic.FunctionalExtensionality Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=WriterTm *)
Inductive WriterTm A :=
| writerRetn (x: A)
| writerNext (b: BYTE) (w: WriterTm A)
| writerSkip (w: WriterTm A)
| writerCursor (w: DWORDCursor -> WriterTm A)
| writerFail.
Class Writer T := getWriterTm: T -> WriterTm unit.
(*=End *)
Implicit Arguments writerFail [[A]].

Fixpoint writerTmBind X Y (w: WriterTm X) (f: X -> WriterTm Y) : WriterTm Y :=
  match w with
  | writerRetn x => f x
  | writerNext b w' => writerNext b (writerTmBind w' f)
  | writerSkip w' => writerSkip (writerTmBind w' f)
  | writerCursor w' => writerCursor (fun p => writerTmBind (w' p) f)
  | writerFail => writerFail
  end.

Fixpoint writerTmSkipFree X (w: WriterTm X) :=
match w with
| writerRetn _ | writerFail => True
| writerSkip _ => False
| writerNext _ w => writerTmSkipFree w
| writerCursor w => forall p, writerTmSkipFree (w p)
end.

Instance writerTmMonadOps : MonadOps WriterTm :=
{ retn := @writerRetn
; bind := writerTmBind }.

Instance writerTmMonad : Monad WriterTm.
Proof. apply Build_Monad.
(* id_l *)
  move => X Y x f. done.
(* id_r *)
  move => X. elim => //=.
  - by move => b w' /= ->.
  - move => w' /= IH. by apply f_equal.
  - move => w' /= IH. apply f_equal. apply functional_extensionality => p. by rewrite IH.
(* assoc *)
  move => X Y Z. elim => //.
  - move => b w' /= IH f g. by rewrite IH.
  - move => w' /= IH f g.
    by apply f_equal.
  - move => w' /= IH f g. apply f_equal. apply functional_extensionality => p.
    by rewrite IH.
Qed.

Definition getWCursor : WriterTm (DWORDCursor) := writerCursor (fun p => writerRetn p).
Definition writeNext {T} {W: Writer T}: Writer T := W.

(* Functional interpretation of writer on sequences *)
Fixpoint runWriterTm padSkip X (w: WriterTm X) (c: DWORDCursor) : option (X * seq BYTE) :=
  match w with
  | writerRetn x => Some (x, nil)
  | writerNext byte w =>
    if c is mkCursor p
    then
      if runWriterTm padSkip w (next p) is Some (x, bytes) then Some (x, byte::bytes) else None
    else None
  | writerSkip w =>
    if c is mkCursor p
    then
      if padSkip
      then if runWriterTm padSkip w (next p) is Some (x, bytes)
           then Some (x, #0::bytes) else None
      else runWriterTm padSkip w (next p)
    else None
  | writerFail => None
  | writerCursor w => runWriterTm padSkip (w c) c
  end.

Lemma runWriterTm_bindCursor padSkip X (w: DWORDCursor -> WriterTm X) (p: DWORD) :
  runWriterTm padSkip (let! c = getWCursor; w c) p =
  runWriterTm padSkip (w p) p.
Proof. done. Qed.

Lemma runWriterTm_bind padSkip X Y (w1: WriterTm X) (w2: X -> WriterTm Y) p y bytes:
  runWriterTm padSkip (let! x = w1; w2 x) p = Some (y, bytes) ->
  exists x p' bytes1 bytes2,
    runWriterTm padSkip w1 p = Some (x, bytes1) /\
    runWriterTm padSkip (w2 x) p' = Some (y, bytes2) /\
    bytes = bytes1 ++ bytes2.
Proof.
  revert p bytes. induction w1 => p bytes Hrun //=.
  - exists x, p, nil, bytes. rewrite Hrun. by eauto.
  - simpl in Hrun. destruct p as [p|]; last done.
    revert Hrun.
    case Hrun': (runWriterTm _ (writerTmBind w1 w2) (next p)) => [[y' bytes']|];
        last done.
    move=> [Hy' Hbytes]. subst y' bytes.
    apply IHw1 in Hrun' as [x [p' [bytes1 [bytes2 IH]]]].
    case: IH => Hw1 [Hw2 Hbytes'] => {IHw1}.
    do 4 eexists. rewrite Hw1. split; first done. split; first eassumption.
    rewrite Hbytes'. done.
  - simpl in Hrun. destruct p => //.
    destruct padSkip.
    * case Hrun': (runWriterTm true (writerTmBind w1 w2) (next p)) => [[y' bytes']|].
      rewrite Hrun' in Hrun. injection Hrun => [H1 H2]. subst.
      specialize (IHw1 (next p) _ Hrun').
      destruct IHw1 as [x [p' [bytes1 [bytes2 [H1 [H2 H3]]]]]].
      do 4 eexists. rewrite H1. split; first done. split; first eassumption. by subst.
      by rewrite Hrun' in Hrun.
    * by apply: IHw1.
  - simpl in Hrun.
    apply H in Hrun as [x [p' [bytes1 [bytes2 IH]]]].
    case: IH => Hw1 [Hw2 Hbytes'] => {H}.
    eauto 10.
Qed.

Definition runWriter padSkip T (w: Writer T) (c: DWORDCursor) (x: T): option (seq BYTE) :=
  let! (_, bytes) = runWriterTm padSkip (w x) c;
  retn bytes.

(*---------------------------------------------------------------------------
   Writer type class together with BYTE, WORD, DWORD and pad instances
  ---------------------------------------------------------------------------*)

(*=writeDWORD *)
Instance writeBYTE : Writer BYTE | 0 :=
  fun b => writerNext b (writerRetn tt).
Instance writeDWORD : Writer DWORD | 0 := fun d =>
  let: (b3,b2,b1,b0) := split4 8 8 8 8 d in
  do! writeBYTE b0;
  do! writeBYTE b1;
  do! writeBYTE b2;
  do! writeBYTE b3;
  retn tt.
(*=End *)

Instance writeQWORD : Writer QWORD | 0 := fun q =>
  let: (b7,b6,b5,b4,b3,b2,b1,b0) := split8 8 8 8 8 8 8 8 8 q in
  do! writeBYTE b0;
  do! writeBYTE b1;
  do! writeBYTE b2;
  do! writeBYTE b3;
  do! writeBYTE b4;
  do! writeBYTE b5;
  do! writeBYTE b6;
  do! writeBYTE b7;
  retn tt.

Instance writeWORD : Writer WORD := fun w =>
  let: (b1,b0) := split2 8 8 w in
  do! writeNext b0;
  do! writeNext b1;
  retn tt.

(** This must go at a lower level/priority than [writeDWORD] and [writeBYTE] so it is picked up less eagerly. *)
(*Instance writeVWORD s : Writer (VWORD s) | 1 :=
  match s as s return Writer (VWORD s) with
  | OpSize1 => writeBYTE
  | OpSize2 => writeWORD
  | OpSize4 => writeDWORD
  | OpSize8 => writeQWORD
  end.
Implicit Arguments writeDWORDorBYTE [].
*)

Instance writeSkipBYTE : Writer unit :=
  fun _ => writerSkip (writerRetn tt).

Fixpoint writePadWith (b: BYTE) m : Writer unit :=
  fun _ =>
  if m is m'.+1
  then do! writeBYTE b; writePadWith b m' tt
  else retn tt.

Fixpoint writeSkipBy m : Writer unit :=
  fun _ =>
  if m is m'.+1
  then do! writeSkipBYTE tt; writeSkipBy m' tt
  else retn tt.

Definition writePad := writePadWith #0.

Definition writeAlignWith b (m:nat) : Writer unit := fun _ =>
  let! c = getWCursor;
  if c is mkCursor pos
  then writePadWith b (toNat (negB (lowWithZeroExtend m pos))) tt
  else retn tt.

Definition writeAlign := writeAlignWith #0.

Definition writeSkipAlign (m:nat) : Writer unit := fun _ =>
  let! c = getWCursor;
  if c is mkCursor pos
  then writeSkipBy (toNat (negB (lowWithZeroExtend m pos))) tt
  else retn tt.


Fixpoint writeTupleBYTE (m:nat) : Writer (m.-tuple BYTE) :=
  if m is m'.+1
  then fun tup => do! writeBYTE (thead tup); writeTupleBYTE (behead_tuple tup)
  else fun tup => retn tt.

Global Existing Instance writeTupleBYTE.

Fixpoint writeString (n:nat) : Writer string := fun s =>
  if n is n'.+1
  then if s is String c s'
       then do! writeBYTE (fromNat (Ascii.nat_of_ascii c)); writeString n' s'
       else do! writeBYTE #0; writeString n' s
  else retn tt.

Definition writeCString : Writer cstring := fun cs =>
  (fix WS (s:string) :=
  if s is String c s'
  then do! writeBYTE (fromNat (Ascii.nat_of_ascii c)); WS s'
  else writeBYTE #0) cs.

Global Existing Instance writeCString.
