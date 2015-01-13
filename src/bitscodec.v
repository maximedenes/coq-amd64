(*======================================================================================
  Primitive codecs for words etc.
  ======================================================================================*)
From Ssreflect
     Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple.
Require Import cast.
Require Import bitsrep (*bitsprops*) bitsops.

Require Import Coq.Strings.String.
Require Import cast codec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* CAREFUL: Our BITS codec is msb first *)
Definition BITScast n : CAST (BITS n * bool) (BITS n.+1).
Proof.
  apply: MakeCast (fun p:BITS n * bool => [tuple of p.2 :: p.1])
                  (fun d => Some (splitlsb d)) _.
  move => t y [<-] /=; rewrite /splitlsb/= -tuple_eta //.
Defined.

Fixpoint bitsCodec n : Codec (BITS n) :=
  if n is n'.+1
  then bitsCodec n' $ Any ~~> BITScast n'
  else always nilB.

Hint Resolve totalCast totalEmp totalSeq totalAny totalSym totalConstSeq.

Lemma totalBITS n : total (bitsCodec n).
Proof.
  induction n => //=.
apply totalCast. apply totalEmp.
move => c. by rewrite (tuple0 c).
apply totalCast. apply totalSeq. apply IHn. apply totalAny.
done.
Qed.

Definition BYTECodec: Codec BYTE := bitsCodec 8.

Corollary totalBYTE : total BYTECodec. Proof. apply totalBITS. Qed.

Definition DWORD_as_BYTES : CAST (BYTE*BYTE*BYTE*BYTE) DWORD.
Proof. apply: MakeCast
  (fun p => let: (b0,b1,b2,b3) := p in b3 ## b2 ## b1 ## b0)
  (fun d => let: (b3,b2,b1,b0) := split4 8 8 8 8 d in Some(b0,b1,b2,b3)) _.
move => d [[[b0 b1] b2] b3]. case E: (split4 8 8 8 8 d) => [[[b0' b1'] b2'] b3'].
move => [<- <- <- <-]. admit. (*by rewrite -(split4eta d) E.*)
Defined.

(* Little-endian DWORDs *)
Definition DWORDCodec: Codec DWORD :=
  BYTECodec $ BYTECodec $ BYTECodec $ BYTECodec ~~> DWORD_as_BYTES.

Lemma totalDWORD: total DWORDCodec.
Proof. apply totalCast. apply totalSeq. apply totalSeq. apply totalSeq.
apply totalBITS. apply totalBITS. apply totalBITS. apply totalBITS. done.
Qed.

Definition WORD_as_BYTES : CAST (BYTE*BYTE) WORD.
Proof. apply: MakeCast
  (fun p => let: (b0,b1) := p in b1 ## b0)
  (fun d => let: (b1,b0) := split2 8 8 d in Some(b0,b1))
  _.
move => d y. case E: (split2 8 8 d) => [b0' b1'].
move => [<-]. admit. (*rewrite (split2eta d). rewrite /split2 in E. congruence. *)
Defined.

(* Little-endian WORDs *)
Definition WORDCodec: Codec WORD :=
  BYTECodec $ BYTECodec ~~> WORD_as_BYTES.

Lemma totalWord : total WORDCodec.
Proof. apply totalCast. apply totalSeq. apply totalBITS. apply totalBITS.
done.
Qed.

Definition shortDWORDEmb : CAST BYTE DWORD.
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
Proof. move => d b/= H. admit. (*by apply signTruncateK. *) Defined.

Definition shortDWORDCodec: Codec DWORD :=
  BYTECodec ~~> shortDWORDEmb.

(*Definition DWORDorBYTECodec dword : Codec (DWORDorBYTE dword) :=
  if dword as dword return Codec (DWORDorBYTE dword)
  then DWORDCodec
  else BYTECodec.

Lemma totalDWORDorBYTE d : total (DWORDorBYTECodec d).
Proof. case d. apply totalDWORD. apply totalBITS. Qed.
*)

Fixpoint Const n : BITS n -> Codec unit :=
  if n is n'.+1
  then fun c => Const (behead_tuple c) .$ Sym (thead c)
  else fun c => Emp.

Coercion Const : BITS >-> Codec.

Lemma totalConst n (c: BITS n) : total (Const c).
Proof. induction n.
+ apply totalEmp.
+ simpl. apply totalConstSeq. apply IHn. apply totalSym.
Qed.

Lemma domConstSeq n (b: BITS n) T (c2: Codec T) : dom (Const b .$ c2) = dom c2.
Proof. by rewrite domCast domSeq /= totalConst. Qed.
