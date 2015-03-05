(*======================================================================================
  Primitive codecs for words etc.
  ======================================================================================*)
From Ssreflect
    Require Import ssreflect ssrfun seq ssrbool ssrnat fintype eqtype tuple.
From Coq
     Require Import Strings.String.
Require Import bitsrep.
Require Import cast codec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Our BITS codec is msb first *)
Definition BITScast n : CAST (BITS n * bool) (BITS n.+1).
Proof. apply: MakeCast (fun p => cons_tuple p.2 p.1) (fun d => Some (splitlsb d)) _.
move => t y [<-]. admit. (*by rewrite /splitlsb/= {3}(tuple_eta t).*) Defined.

Fixpoint bitsCodec n : Codec (BITS n) :=
  if n is n'.+1
  then bitsCodec n' $ Any ~~> BITScast n'
  else always nilB.

Hint Resolve totalCast totalEmp totalSeq totalAny totalSym totalConstSeq.

Lemma totalBITS n : total (bitsCodec n).
Proof. induction n => //=.
apply totalCast. apply totalEmp.
move => c. by rewrite (tuple0 c).
apply totalCast. apply totalSeq. apply IHn. apply totalAny.
done.
Qed.

Definition BYTECodec: Codec BYTE := bitsCodec 8.

Corollary totalBYTE : total BYTECodec. Proof. apply totalBITS. Qed.

Definition BITS_as_BYTES n : CAST (n.-tuple BYTE) (BITS (n * 8)).
Proof. admit. (* apply: (MakeCast (@bytesToBits n) (fun d => Some (bitsToBytes n d)) _).
move => x y [<-]. apply bitsToBytesK.  *)
Defined.

(*Require Import tuplehelp.*)
Definition consTupleCast {n X} : CAST (X * n.-tuple X) (n.+1.-tuple X).
Proof. apply: MakeCast (fun p => cons_tuple p.1 p.2) (fun d => Some (thead d, behead_tuple d)) _.
move => t y [<-]/=. case/tupleP: t => [x xs]. admit. (*by rewrite theadCons beheadCons. *) Defined. 

Definition nilTupleCast {X} : CAST unit (0.-tuple X).
Proof. apply: MakeCast (fun p => nil_tuple _) (fun d => Some tt) _. 
move => t y []/=. by rewrite (tuple0 t). Defined. 

Fixpoint tupleCodec X n (c: Codec X) : Codec (n.-tuple X) :=
  if n is n'.+1 return Codec (n.-tuple X)
  then c $ tupleCodec n' c ~~> consTupleCast 
  else Emp ~~> nilTupleCast.

(* Little-endian DWORDs *)
Definition DWORDCodec: Codec DWORD :=
  tupleCodec 4 BYTECodec ~~> BITS_as_BYTES _.

Definition QWORDCodec: Codec QWORD :=
  tupleCodec 8 BYTECodec ~~> BITS_as_BYTES _.

(*
Lemma totalDWORD: total DWORDCodec.
Proof. apply totalCast. apply totalSeq. apply totalSeq. apply totalSeq.
apply totalBITS. apply totalBITS. apply totalBITS. apply totalBITS. done.
Qed.
*)

(* Little-endian WORDs *)
Definition WORDCodec: Codec WORD :=
  tupleCodec 2 BYTECodec ~~> BITS_as_BYTES _.

(*
Lemma totalWord : total WORDCodec.
Proof. apply totalCast. apply totalSeq. apply totalBITS. apply totalBITS.
done.
Qed.
*)

Definition shortDWORDEmb : CAST BYTE DWORD.
apply: MakeCast (@signExtend 24 7) (@signTruncate 24 7) _.
Proof. admit. (* move => d b/= H. by apply signTruncateK.*) Defined.

Definition shortDWORDCodec: Codec DWORD :=
  BYTECodec ~~> shortDWORDEmb.

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
