From Ssreflect
     Require Import ssreflect ssrfun seq ssrbool ssrnat fintype eqtype tuple.
From Coq
     Require Import Strings.String Setoids.Setoid
     Classes.Morphisms Classes.RelationClasses
     Logic.FunctionalExtensionality.
Require Import cast.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*======================================================================================
  Concrete syntax for *partial* two-way codecs
  (partial in the sense that they only encode a subset of values)

  This is very similar to the Rocksalt grammar type, except that Map is generalized to
  use CASTs so that we can *encode* values as well as decode them.

  Other possibilities
  - n-ary Alt, with Void just sugar for Alt nil
  - n-ary Seq, with Emp just sugar for Seq nil (but consider types)
  ======================================================================================*)
Definition sym := bool.

Inductive Codec : Type -> Type :=
| Any : Codec sym
| Sym :> sym -> Codec unit
| Emp : Codec unit
| Void T : Codec T
| Seq T U (c: Codec T) (d: Codec U) : Codec (T*U)
(*| Dep (T:finType) F (c: Codec T) (d: forall x:T, Codec (F x)) : Codec {x:T & F x}*)
| Alt T : Codec T -> Codec T -> Codec T
| Star T : Codec T -> Codec (seq T)
| Cast T U: CAST T U -> Codec T -> Codec U
.

(* Some nice syntax *)
Notation "x $ y"   := (Seq x y)   (left associativity, at level 42).
Notation "x ~~> f" := (Cast f x)  (left associativity, at level 50).
Notation "x ||| y" := (Alt x y)   (at level 55).


Notation "x .$ y" := (Seq x y ~~> sndUnitCast _) (at level 30).
Notation "x $. y" := (Seq x y ~~> fstUnitCast _) (at level 30).

(* Constant parser *)
Definition always (t: eqType) x : Codec t :=
    Emp ~~> unConst x.

Definition alwaysNone {t} := 
    Emp ~~> (@unNone t).

(* Use one bit to dispatch to left or right summand *)
Definition SumCond T U (c: Codec T) (d: Codec U) : Codec (T+U) :=
    Sym false .$ c ~~> unInl _ _
||| Sym true  .$ d ~~> unInr _ _.

(* Codec for sigma type whose first component is a boolean *)
Definition DepCond F (c: forall x:bool, Codec (F x)) : Codec {x:bool & F x}:=
    SumCond (c false) (c true) ~~> sumCast F.

(* Non-dependent conditional *)
Definition Cond X (c:bool->Codec X) : Codec X :=
    Sym false .$ c false
||| Sym true  .$ c true.

(*
Definition SimpleDep (T:finType) U (c: Codec T) (d: T -> Codec U) : Codec (T*U) :=
  Dep c d ~~> existTcast T U.
*)

(* Example of a non-prefix but uniquely-decodeable codec *)
Example nonprefix : Codec bool :=
    Sym false             ~~> unConst false
||| Sym false .$ Sym false ~~> unConst true.

(* We define the interpretation by a fixpoint rather than an inductive family because
   inversion has trouble with the latter when it is GADT-style *)
Fixpoint interps t interp (l: seq sym) (xs: seq t) : Prop :=
  if xs is x::xs'
  then exists s l1 l2, l = s::(l1++l2) /\ interp (s::l1) x /\ interps interp l2 xs'
  else l = nil.

Fixpoint interp t (c: Codec t){struct c} : seq sym -> t -> Prop :=
match c in Codec t return seq sym -> t -> Prop with
| Any          => fun l b => l = b::nil
| Emp          => fun l _ => l = nil
| Sym b        => fun l _ => l = b::nil
| Void _       => fun l _ => False
| Cast T U f c => fun l v => exists w, v = upcast f w /\ interp c l w
| Alt _ c d    => fun l v => interp c l v \/ interp d l v
| Seq _ _ c d  => fun l v => exists l1 l2, l = l1++l2 /\ interp c l1 v.1 /\ interp d l2 v.2
(*| Dep _ _ c d  => fun l v => let: existT x w := v in
                             exists l1 l2, l = l1++l2 /\ interp c l1 x /\ interp (d x) l2 w*)
| Star T c     => fun l v => interps (interp c) l v
end.

(* This is the inductive version
Inductive interp : forall t, Codec t -> seq sym -> t -> Prop :=
| interp_Any b : @interp sym Any [::b] b
| interp_Emp : interp Emp nil tt
| interp_Sym b : interp (Sym b) [::b] tt
| interp_Cast T U f c w l : interp c l w -> interp (@Cast T U f c) l (upcast f w)
| interp_Alt1 T c d l v : interp c l v -> interp (@Alt T c d) l v
| interp_Alt2 T c d l v : interp d l v -> interp (@Alt T c d) l v
| interp_Seq T U c d l1 l2 v1 v2 : interp c l1 v1 -> interp d l2 v2 -> interp (@Seq T U c d) (l1++l2) (v1,v2)
| interp_StarNil T (c:Codec T) : interp (Star c) nil nil
| interp_StarCons T (c:Codec T) s l1 l2 x xs : interp c (s::l1) x -> interp (Star c) l2 xs -> interp (Star c) (s::(l1++l2)) (x::xs)
.
*)

(* Simplification lemms for interpretation *)
Lemma interpAny l b : interp Any l b <-> l = [::b].
Proof. done. Qed.

Lemma interpEmp l   : interp Emp l tt <-> l = nil.
Proof. done. Qed.

Lemma interpSym b l : interp (Sym b) l tt <-> l = [::b].
Proof. done. Qed.

Lemma interpVoid t l (x:t) : interp (Void _) l x <-> False.
Proof. done. Qed.

Lemma interpAlt t (c1 c2: Codec t) (l: seq sym) x:
  interp (Alt c1 c2) l x <-> interp c1 l x \/ interp c2 l x.
Proof. done. Qed.

Lemma interpSeq t1 t2 (c1: Codec t1) (c2: Codec t2) l x:
  interp (Seq c1 c2) l x <-> exists l1 l2, l = l1++l2 /\ interp c1 l1 x.1 /\ interp c2 l2 x.2.
Proof. done. Qed.

Lemma interpSeqSym t (c: Codec t) s (l: seq sym) x:
  interp (Seq (Sym s) c) l (tt,x) <-> exists l', l = s::l' /\ interp c l' x.
Proof. rewrite interpSeq /=.
split. move => [l1 [l2 [H1 [H2 H3]]]]. subst. firstorder.
move => [l' [H1 H2]]. subst. exists [::s]. exists l'. split => //.
Qed.

Lemma interpCast t u (c: Codec t) (f: CAST t u) l v:
  interp (Cast f c) l v <-> exists w, v = upcast f w /\ interp c l w.
Proof. split => H. destruct H as [w H]. by exists w.
destruct H as [w [H1 H2]]. subst. firstorder. Qed.

Lemma interpStar t (c: Codec t) (l: seq sym) xs :
  interp (Star c) l xs <->
  match l, xs with s::l', x::xs' =>
    (exists l1 l2, l' = l1++l2 /\ interp c (s::l1) x /\ interp (Star c) l2 xs')
  | nil, nil => True
  | _, _ => False
  end.
Proof. induction xs. destruct l => //.
split => //.
destruct l => //. by move => [s [l1 [l2 [H1 H2]]]].
simpl. move => [s' [l1 [l2 [H1 [H2 H3]]]]]. inversion H1. subst.
exists l1, l2. firstorder.
destruct l => //. move => [l1 [l2 [H1 [H2 H3]]]]. subst.
simpl. exists s, l1, l2. firstorder.
Qed.

Hint Rewrite interpAny interpEmp interpSym interpVoid interpAlt
             interpSeqSym interpSeq interpCast interpStar : interp.

(*======================================================================================
  Size analysis
  ======================================================================================*)
Fixpoint maxSize t (c:Codec t) : option nat :=
match c with
| Any     => Some 1
| Emp     => Some 0
| Sym b  => Some 1
| Void _ => Some 0
| Alt _ c d => if maxSize c is Some x then if maxSize d is Some y then Some (maxn x y) else None else None
| Seq t1 t2 c d =>
  if maxSize c is Some x then if maxSize d is Some y then Some (x + y) else None else None
(*| Dep t1 t2 c1 c2 =>
  let xs := Finite.mixin_enum (Finite.class t1) in
  foldr (fun x n => max (maxSize (c2 x)) n) (maxSize c1) xs*)
| Cast _ _ g c => maxSize c
| Star _ _ => None
end.

Definition finiteCodec t (c: Codec t) := maxSize c <> None.

Lemma finiteCodecSeq t u (c: Codec t) (d: Codec u) :
  finiteCodec (c $ d) <-> finiteCodec c /\ finiteCodec d.
Proof. rewrite /finiteCodec/=.
destruct (maxSize c) => //. destruct (maxSize d) => //. intuition. intuition.
Qed.

Lemma finiteCodecAlt t (c d: Codec t) :
  finiteCodec (c ||| d) <-> finiteCodec c /\ finiteCodec d.
Proof. rewrite /finiteCodec/=.
destruct (maxSize c) => //. destruct (maxSize d) => //. intuition. intuition.
Qed.

Lemma finiteCodecCast t u (c: Codec t) (f: CAST t u):
  finiteCodec (c ~~> f) <-> finiteCodec c.
Proof. by rewrite /finiteCodec/=. Qed.

Fixpoint minSize t (c:Codec t) : nat :=
match c with
| Any     => 1
| Emp     => 0
| Sym b  => 1
| Void _ => 0
| Alt _ c d => minn (minSize c) (minSize d)
| Seq t1 t2 c1 c2 => minSize c1 + minSize c2
(*| Dep t1 t2 c1 c2 =>
  let xs := Finite.mixin_enum (Finite.class t1) in
  foldr (fun x n => min (minSize (c2 x)) n) (minSize c1) xs*)
| Cast _ _ g c => minSize c
| Star _ _ => 0
end.

Lemma minSizeSound t (c: Codec t) : forall l x, interp c l x -> size l >= minSize c.
Proof. induction c => l x /=H.
- by subst. - by subst. - by subst. - done.
- elim H => [l1 [l2 [-> [H2 H3]]]].
  specialize (IHc1 _ _ H2).
  specialize (IHc2 _ _ H3).
  rewrite size_cat. apply leq_add => //.
- elim H => H'.
  specialize (IHc1 _ _ H'). by rewrite geq_min IHc1.
  specialize (IHc2 _ _ H'). by rewrite geq_min IHc2 orbT.
- done.
- elim H => [w [H1 H2]]. apply: IHc H2.
Qed.

Lemma maxSizeSound t (c: Codec t) :
  forall n, maxSize c = Some n -> forall l x, interp c l x -> size l <= n.
Proof. induction c => n /=EQ l x /=H.
- injection EQ => <-. by subst.
- injection EQ => <-. by subst.
- by subst.
- done.
- elim H => [l1 [l2 [-> [H2 H3]]]].
  case E1: (maxSize c1) => [n1 |]; rewrite E1 in EQ => //.
  case E2: (maxSize c2) => [n2 |]; rewrite E2 in EQ => //.
  specialize (IHc1 _ E1 _ _ H2).
  specialize (IHc2 _ E2 _ _ H3).
  rewrite size_cat.
  injection EQ => <-. apply leq_add => //.
- case E1: (maxSize c1) => [n1 |]; rewrite E1 in EQ => //.
  case E2: (maxSize c2) => [n2 |]; rewrite E2 in EQ => //.
  elim H => H'.
  * specialize (IHc1 _ E1 _ _ H'). injection EQ => <-. by rewrite leq_max IHc1.
  * specialize (IHc2 _ E2 _ _ H'). injection EQ => <-. by rewrite leq_max IHc2 orbT.
- done.
- elim H => [w [H1 H2]]. apply: IHc H2 => //.
Qed.

Fixpoint consSize m ms :=
  if ms is n::ms' then
    if m < n then m::ms
    else if m == n then ms
    else n::consSize m ms' else [::m].

Fixpoint unionSizes (ms ns : seq nat) :=
  if ms is n::ms' then unionSizes ms' (consSize n ns) else ns.

Fixpoint addToSizes m ns :=
  if ns is n::ns' then m+n::addToSizes m ns' else nil.

Fixpoint addSizes ms ns :=
  if ms is m::ms' then unionSizes (addSizes ms' ns) (addToSizes m ns) else nil.

Fixpoint sizes t (c:Codec t) : seq nat :=
match c with
| Any     => [::1]
| Emp     => [::0]
| Sym b  => [::1]
| Void _ => [::0]
| Alt _ c d => unionSizes (sizes c) (sizes d)
| Seq t1 t2 c d => addSizes (sizes c) (sizes d)
| Cast _ _ g c => sizes c
| Star _ _ => nil
end.

Require Import Ssreflect.div.
(* Compute minimum, maximum, and gcd of number of bits *)
Definition stats t (c: Codec t) :=
  let s := sizes c
  in (head 0 s, last 0 s, foldr gcdn 0 s).

Lemma consSizeMem x xs : forall y, x \in xs -> x \in consSize y xs.
Proof. induction xs => // => x' MEM/=.
case (x' < a). rewrite in_cons. by rewrite MEM orbT.
case (x' == a) => //. rewrite in_cons. apply/orP. rewrite in_cons in MEM.
case/orP: MEM => H1. by left. right. by apply IHxs.
Qed.

Lemma consSizeMemHead x xs : x \in consSize x xs.
Proof. induction xs => //=. by rewrite in_cons eq_refl.
case (x < a). by rewrite in_cons eq_refl.
case E: (x == a). rewrite (eqP E). by rewrite in_cons eq_refl.
rewrite in_cons. apply/orP. by right.
Qed.

Lemma unionSizesMemR x xs : forall ys, x \in ys -> x \in unionSizes xs ys.
Proof. induction xs => //=. move => ys MEM. apply IHxs. destruct ys => //.
by apply consSizeMem. Qed.

Lemma unionSizesMemL x xs: forall ys, x \in xs -> x \in unionSizes xs ys.
Proof. induction xs => //= ys. rewrite in_cons.
case/orP. move/eqP ->. apply unionSizesMemR. apply consSizeMemHead. apply IHxs. Qed.

Lemma addToSizesMem a y ys : y \in ys -> a+y \in addToSizes a ys.
Proof. induction ys => //= H.
rewrite in_cons in H.
case/orP: H => H'.
rewrite (eqP H'). by rewrite mem_head.
rewrite in_cons.
apply/orP. right. by apply IHys.
Qed.

Lemma addSizesMem (x y:nat) xs: forall ys, x \in xs -> y \in ys -> x+y \in addSizes xs ys.
Proof. induction xs => //= ys.
rewrite in_cons. case/orP.
move/eqP => ->. move => H1. apply unionSizesMemR. by apply addToSizesMem.
move => Hx Hy. apply unionSizesMemL. by apply IHxs.
Qed.

Lemma sizesSound t (c: Codec t) :
  finiteCodec c ->
  forall l x, interp c l x -> size l \in sizes c.
Proof. induction c => FIN /= l x /=H.
- by subst.
- by subst.
- by subst.
- done.
- elim H => [l1 [l2 [-> [H2 H3]]]].
  apply finiteCodecSeq in FIN. elim FIN => [FIN1 FIN2].
  specialize (IHc1 FIN1 _ _ H2).
  specialize (IHc2 FIN2 _ _ H3).
  rewrite size_cat.
  by apply addSizesMem.
- apply finiteCodecAlt in FIN. elim FIN => [FIN1 FIN2].
  elim H => H'.
  * specialize (IHc1 FIN1 _ _ H'). by apply unionSizesMemL.
  * specialize (IHc2 FIN2 _ _ H'). by apply unionSizesMemR.
- by rewrite /finiteCodec in FIN.
- elim H => {H} [w [H1 H2]].
  apply finiteCodecCast in FIN.
  apply: IHc H2 => //.
Qed.

Lemma sizesProp t (c: Codec t) P :
  finiteCodec c ->
  all P (sizes c) ->
  forall l x, interp c l x -> P (size l).
Proof. admit. (* move => FIN ALL l x I.
have SS:= sizesSound FIN I.
apply: allP. apply ALL. done.  *) Qed.

(*======================================================================================
  Semantic equivalence of codecs
  ======================================================================================*)
Definition codecEq t (c1 c2: Codec t) := forall l x, interp c1 l x <-> interp c2 l x.
Notation "x '===' y" := (codecEq x y) (at level 70, no associativity).

(* It's an equivalence relation *)
Global Instance codecEqEqu t : Equivalence (@codecEq t).
Proof. constructor; red; rewrite /codecEq.
+ done.
+ firstorder.
+ move => c1 c2 c3 H1 H2 l x. specialize (H1 l x). specialize (H2 l x). firstorder.
Qed.

(* It's preserved by constructors *)
Global Instance codecEq_seq_m t u:
  Proper (@codecEq t ==> @codecEq u ==> @codecEq _) (@Seq t u).
Proof. move => p1 p2 EQ1 q1 q2 EQ2 .
move => l [x y].
autorewrite with interp. split => /= H /=. destruct H as [l1 [l2 [H1 [H2 H3]]]].
exists l1, l2. rewrite /codecEq in EQ1, EQ2. firstorder.
destruct H as [l1 [l2 [H1 [H2 H3]]]].
exists l1, l2. rewrite /codecEq in EQ1, EQ2. firstorder.
Qed.

Global Instance codecEq_alt_m t:
  Proper (@codecEq t ==> @codecEq t ==> @codecEq _) (@Alt t).
Proof. move => p1 p2 EQ1 q1 q2 EQ2 .
move => l x.
autorewrite with interp. split => /= H /=. rewrite /codecEq in EQ1, EQ2. firstorder.
rewrite /codecEq in EQ1, EQ2. firstorder.
Qed.

Global Instance codecEq_cast_m t u:
  Proper (eq ==> @codecEq _ ==> @codecEq _) (@Cast t u).
Proof. move => p1 p2 EQ1 q1 q2 EQ2.
move => l x. autorewrite with interp.
split => /= H /=.
destruct H as [w [H1 H2]]. exists w. subst. firstorder.
destruct H as [w [H1 H2]]. exists w. subst. firstorder.
Qed.

Global Instance codecEq_interp_m t: Proper (@codecEq t ==> eq ==> eq ==> iff) (@interp t).
Proof. move => r1 r2 EQ l1 l2 -> x1 x2 ->.
rewrite /codecEq in EQ. firstorder.
Qed.


(* Commutativity, associativity, idempotence and unit for Alt *)
Lemma AltC t (c d: Codec t) : c ||| d === d ||| c.
Proof. move => l x. autorewrite with interp. split => /= H; intuition. Qed.

Lemma AltA t (c d e: Codec t) : c ||| d ||| e === c ||| (d ||| e).
Proof. move => l x. autorewrite with interp. split => /= H; intuition. Qed.

Lemma AltN t (c d e: Codec t) : c ||| c === c.
Proof. move => l x. autorewrite with interp. split => /= H; intuition. Qed.

Lemma AltVoid t (c: Codec t) : c ||| Void _ === c.
Proof. move => l x. autorewrite with interp. split => /= H; intuition. Qed.

Lemma VoidAlt t (c: Codec t) : Void _ ||| c === c.
Proof. move => l x. autorewrite with interp. split => /= H; intuition. Qed.

(* Push cast into Alt *)
Lemma CastAlt t u (f: CAST t u) (c: Codec t) (d: Codec t) :
  (c ||| d) ~~> f === (c ~~> f) ||| (d ~~> f).
Proof. move => l x. autorewrite with interp. split => /= H; destruct H; firstorder. Qed.

(* Composition of casts *)
Lemma ComposeCast t u v (f:CAST t u) (g: CAST u v) (c: Codec t):
  c ~~> f ~~> g === c ~~> composeCast f g.
Proof. move => l x. autorewrite with interp. split => /= H.
+ destruct H as [w [H1 [w' [H2 H3]]]]. subst. by exists w'.
+ destruct H as [w [H1 H2]]. subst. exists (f w). firstorder.
Qed.

(* Elimination of cast by Void *)
Lemma CastVoid t u f:
  Void t ~~> f === Void u.
Proof. firstorder. Qed.

(* Pulling casts out of Seq *)
Lemma CastSeq t u v (f:CAST t v) (c: Codec t) (d: Codec u) :
  (c ~~> f) $ d === (c $ d) ~~> pairOfCasts f (idCast _).
Proof. move => l [x y]. autorewrite with interp. split => /= H.
destruct H as [l1 [l2 [H1 [H2 H3]]]]. destruct H2 as [w [H4 H5]]. subst.
exists (w, y). firstorder.
destruct H as [[a b] [H1 [l1 [l2 [H2 [H3 H4]]]]]]. subst. simpl in H1, H3, H4.
injection H1 => [-> ->]. exists l1, l2. firstorder.
Qed.

Lemma SeqCast t u v (f:CAST u v) (c: Codec t) (d: Codec u) :
  c $ (d ~~> f) === (c $ d) ~~> pairOfCasts (idCast _) f.
Proof. move => l [x y]. autorewrite with interp. split => /= H.
destruct H as [l1 [l2 [H1 [H2 H3]]]]. destruct H3 as [w [H4 H5]]. subst.
exists (x, w). firstorder.
destruct H as [[a b] [H1 [l1 [l2 [H2 [H3 H4]]]]]]. subst. simpl in H1, H3, H4.
injection H1 => [-> ->]. exists l1, l2. firstorder.
Qed.

(* Common prefix under Alt *)
Lemma SeqAlt t u (b:Codec u) (c d: Codec t):
  b $ (c ||| d) === b $ c ||| b $ d.
Proof. move => l x. autorewrite with interp. firstorder. Qed.

(* Common postfix under Alt *)
Lemma AltSeq t u (b:Codec u) (c d: Codec t):
  (c ||| d) $ b === c $ b ||| d $ b.
Proof. move => l x. autorewrite with interp. firstorder. Qed.

(* Special case for .$ *)
Lemma CastConstSeq t u (c: Codec _) (d: Codec t) (f: CAST t u) :
  c .$ d ~~> f ===  c .$ (d ~~> f).
Proof. move => l x. autorewrite with interp.
split => /= H. destruct H as [w [EQ H]]. autorewrite with interp in H.
destruct H as [w' [EQ' H]]. autorewrite with interp in H.
destruct H as [l1 [l2 [H1 [H2 H3]]]].
exists (tt,x). split => //.
autorewrite with interp. exists l1, l2. split => //. split => //. subst. simpl.
destruct w' as [u' w']. simpl in H2.
destruct u'. done.
autorewrite with interp. exists w. split => //. by  subst.

destruct H as [w [EQ H]]. autorewrite with interp in H.
destruct H as [l1 [l2 [H1 [H2 H3]]]].
autorewrite with interp in H3. destruct H3 as [w' [H3 H4]]. subst.
exists w'. split => //. autorewrite with interp. exists (tt,w'). split => //.
autorewrite with interp. exists l1, l2. split => //.
split => //. simpl. by destruct w as [[] w].
Qed.

Lemma SeqEmp t (c: Codec t) :
  c $ Emp === c ~~> unitRcast _.
Proof. move => l [x []]. autorewrite with interp. split.
+ move => [l1 [l2 [H1 [H2 H3]]]]. exists x. simpl in H3. subst. rewrite cats0. firstorder.
+ move => [w [H1 H2]]. simpl in H1. injection H1 => [->]. exists l, nil. firstorder.
Qed.

Lemma EmpSeq t (c: Codec t) :
  c ~~> unitLcast _ === Emp $ c.
Proof. move => l [[] x]. autorewrite with interp. split.
+ move => [w [H1 H2]]. simpl in H1. injection H1 => [->]. exists nil, l. firstorder.
+ move => [l1 [l2 [H1 [H2 H3]]]]. exists x. simpl in H2. subst. firstorder.
Qed.

Lemma SeqAssoc t1 t2 t3 (c1: Codec t1) (c2: Codec t2) (c3: Codec t3) :
  c1 $ c2 $ c3 === c1 $ (c2 $ c3) ~~> pairAssocCast _ _ _.
Proof. move => l. move => [[x y] z]. autorewrite with interp. split.
+ move => [l1 [l2 [H1 [H2 H3]]]]. subst. exists (x,(y,z)).
  destruct H2 as [l3 [l4 [H4 [H5 H6]]]]. subst. rewrite -catA.
  split => //. exists l3, (l4++ l2). firstorder.
+ move => [w [H1 H2]]. simpl in H2. destruct H2 as [l1 [l2 [H3 [H4 H5]]]]. subst.
  destruct H5 as [l3 [l4 [H6 [H7 H8]]]]. subst. exists (l1++l3),l4. rewrite catA.
  split => //. injection H1 => [-> -> ->]. firstorder.
Qed.

Lemma VoidSeq t u (c: Codec t) : Void u $ c === Void _.
Proof. firstorder. Qed.

Lemma SeqVoid t u (c: Codec t) : c $ Void u === Void _.
Proof. firstorder. Qed.

(*======================================================================================
  Smart constructors
  ======================================================================================*)
Fixpoint cSeq t1 t2 (r1:Codec t1) (r2:Codec t2) : Codec (t1*t2) :=
match r1 in Codec t1, r2 in Codec t2 return Codec (t1*t2) with
| _, Void _ => Void _
| Void _, _ => Void _
| Cast _ _ f r1, r2 => cSeq r1 r2 ~~> pairOfCasts f (idCast _)
| Emp, r2 => r2 ~~> unitLcast _
| r1, Emp => r1 ~~> unitRcast _
| Seq _ _ r1a r1b, r2 => cSeq r1a (cSeq r1b r2) ~~> pairAssocCast _ _ _
| r1, r2 => Seq r1 r2
end.

Lemma cSeqSound t (c: Codec t) : forall u (d: Codec u), cSeq c d === Seq c d.
Proof.
induction c => u d.
+ destruct d => //=. by rewrite SeqEmp. by rewrite SeqVoid.
+ destruct d => //=. by rewrite SeqEmp. by rewrite SeqVoid.
+ rewrite <-EmpSeq. destruct d => //=. by rewrite CastVoid.
+ rewrite VoidSeq. by destruct d => //=.
+ destruct d => //=. by rewrite SeqAssoc -IHc2 -IHc1.
  by rewrite SeqAssoc -IHc2 -IHc1.
  by rewrite SeqEmp. by rewrite SeqVoid.
  by rewrite SeqAssoc -IHc2 -IHc1.
  by rewrite SeqAssoc -IHc2 -IHc1.
  by rewrite SeqAssoc -IHc2 -IHc1.
  by rewrite SeqAssoc -IHc2 -IHc1.
+ destruct d => //=. by rewrite SeqEmp. by rewrite SeqVoid.
+ destruct d => //=. by rewrite SeqEmp. by rewrite SeqVoid.
+ rewrite CastSeq -IHc. destruct d => //=. rewrite IHc. by rewrite SeqVoid CastVoid.
Qed.

Fixpoint cAltAux t (r1 r2: Codec t) : Codec t :=
match r1, r2 with
(*
| r1, Void _ => r1
*)
| Void _, r2 => r2
| Alt _ r1a r1b, _ => Alt r1a (cAltAux r1b r2)
| r1, r2 => Alt r1 r2
end.

Lemma cVoidAltSound t (c:Codec t): cAltAux (Void _) c === c.
Proof. by destruct c. Qed.

Lemma cAltAuxSound t c : forall d: Codec t, cAltAux c d === Alt c d.
Proof. induction c => //. move => d. by rewrite cVoidAltSound VoidAlt.
move => d. rewrite AltA. rewrite <- IHc2. destruct d => //.
Qed.

Definition simplCast t (c: Codec t) :=
match c with
| Cast _ _ f (Void _) => Void _
| Cast _ _ f (Cast _ _ g (Void _)) => Void _
| _ => c
end.

Lemma simplCastSound t (c: Codec t) : simplCast c === c.
Proof. destruct c => //=. destruct c0 => //=. rewrite CastVoid => //.
destruct c1 => //=. rewrite CastVoid => //. rewrite CastVoid => //.
Qed.

Definition cAlt t (r1 r2: Codec t) := cAltAux (simplCast r1) (simplCast r2).

Lemma cAltSound t (c d: Codec t): cAlt c d === Alt c d.
Proof. rewrite /cAlt. by rewrite cAltAuxSound 2!simplCastSound. Qed.

Fixpoint cCast t (c: Codec t) : forall u, CAST t u -> Codec u :=
match c in Codec t return forall u, CAST t u -> Codec u with
| Cast t' u' g c => fun _ f => cCast c (composeCast g f)
| c => fun _ f => Cast f c
end.

Lemma cCastSound t (c: Codec t) : forall u (f: CAST t u), cCast c f === Cast f c.
Proof. induction c => // u f. by rewrite /= IHc ComposeCast. Qed.

(* Deterministic language *)
Definition detInterp t (c: Codec t) :=
  forall l v w, interp c l v -> interp c l w -> v=w.

(* Prefix-free language *)
Definition prefixFreeInterp t (c: Codec t) :=
  forall l e v w, interp c l v -> interp c (l++e) w -> e=nil.

(* Deterministic *and* prefix-free *)
Definition dpfInterp t (c: Codec t) :=
  forall l e v w, interp c l v -> interp c (l++e) w -> v=w /\ e=nil.

(*======================================================================================
  Executable encoder function
  ======================================================================================*)
(* Note that we insist that encoding a value in a starred codec actually produces a
non-empty list *)
Fixpoint encs t enc (xs: seq t) : option (seq sym) :=
  if xs is x::xs'
  then if enc x is Some (b::bs) then
       if encs enc xs' is Some bs'
       then Some(b::bs++bs') else None else None
  else Some nil.

Definition encShortest := true.

Fixpoint enc t (c:Codec t) : t -> option (seq sym) :=
match c with
| Any => fun b => Some (b::nil)
| Emp => fun _ => Some nil
| Sym b => fun _ => Some (b::nil)
| Void _ => fun _ => None
| Cast _ _ f c => fun x =>
  if downcast f x is Some y then enc c y else None
| Seq _ _ c d => fun x =>
  let: (y,z) := x in
  if enc c y is Some bs1 then
  if enc d z is Some bs2 then Some (bs1++bs2)
  else None else None
| Alt _ c d => fun x =>
  match enc c x, enc d x with
  | Some bs1, Some bs2 =>
    if size bs1 <= size bs2 then Some bs1 else Some bs2
  | None, Some bs2 => Some bs2
  | Some bs1, None => Some bs1
  | None, None => None
  end
| Star _ c => fun x => encs (enc c) x
end.

Lemma encsSound t (c: Codec t) : (forall v l, enc c v = Some l -> interp c l v) ->
  (forall vs l, encs (enc c) vs = Some l -> interps (interp c) l vs).
Proof. move => H. induction vs => l.
+ destruct l => //.
+ simpl.
  case E1: (enc c a) => [l1 |] => //. specialize (H _ _ E1).
  case E2: (encs (enc c) vs) => [l2 |] => //.  specialize (IHvs _ E2).
  destruct l1 => //. move => [<-].
  exists s, l1, l2. firstorder.
  destruct l1 => //.
Qed.

Lemma encSound t (c: Codec t) : forall v l, enc c v = Some l -> interp c l v.
Proof. admit. (* induction c => v l [/=EQ] /=; autorewrite with interp => /=.
(* Any *)
done.
(* Sym *)
destruct v. subst. constructor.
(* Emp *)
destruct v. subst. constructor.
(* Void *)
done.
(* Seq *)
destruct v as [v1 v2].
case E1: (enc c1 v1) => [l1 |]; rewrite E1 in EQ => //.
case E2: (enc c2 v2) => [l2 |]; rewrite E2 in EQ => //.
exists l1, l2. injection EQ => [<-]. split => //. intuition.
(*(* Dep *)
destruct v as [x w].
case E1: (enc c x) => [l1 |]; rewrite E1 in EQ => //.
case E2: (enc (d x) w) => [l2 |]; rewrite E2 in EQ => //.
exists l1, l2. injection EQ => [<-]. split => //. intuition. *)
(* Alt *)
case E1: (enc c1 v) => [l1 |]; rewrite E1 in EQ => //.
case E2: (enc c2 v) => [l2 |]; rewrite E2 in EQ => //.
case B: (size l1 <= size l2); rewrite B in EQ;
injection EQ => [<-]; intuition.
injection EQ => [<-]; intuition.
case E2: (enc c2 v) => [l2 |]; rewrite E2 in EQ => //.
injection EQ => [<-]; intuition.
(* Star *)
apply encsSound => //.
(* Cast *)
case E: (downcast c v) => [v' |]; rewrite E in EQ => //.
exists v'. have IV := castinv E. intuition. *)
Qed.


(*======================================================================================
  Domain and totality, based on encoding
  ======================================================================================*)
Definition dom t (c: Codec t) : pred t := SimplPred (fun x => isSome (enc c x)).
Definition total t (c: Codec t) := dom c =1 predT.

Lemma domEmp : dom Emp = predT. Proof. done. Qed.
Lemma domAny : dom Any = predT. Proof. done. Qed.
Lemma domSym b : dom (Sym b) = predT. Proof. done. Qed.
Lemma domVoid t : dom (Void t) = [pred _ | false]. Proof. done. Qed.
Lemma domAlt T (c1 c2: Codec T) : dom (c1 ||| c2) = predU (dom c1) (dom c2).
Proof. apply functional_extensionality => x. rewrite /dom/=.
destruct (enc c1 x) => //. destruct (enc c2 x) => //.
by destruct (_ <= _). destruct (enc c2 x) => //.
Qed.

Lemma domSeq T U (c: Codec T) (d: Codec U) : dom (c $ d) = [pred x | dom c x.1 && dom d x.2].
Proof. apply functional_extensionality => x. destruct x as [y z]. simpl.
rewrite /dom/=. destruct (enc c y) => //. destruct (enc d z) => //. Qed.

Lemma domCast T U (c: Codec T) (f: CAST T U) :
  dom (c ~~> f) = [pred u | if downcast f u is Some t then dom c t else false].
Proof. apply functional_extensionality => u.
rewrite /dom/=.
destruct (downcast f u) => //.
Qed.

Lemma totalEmp : total Emp. Proof. done. Qed.
Lemma totalAny : total Any. Proof. done. Qed.
Lemma totalSym b : total (Sym b). Proof. done. Qed.
Lemma totalApp t (c: Codec t) : total c -> forall v, isSome (enc c v). Proof. done. Qed.

Lemma totalCast T U (c: Codec T) (f: CAST T U) : total c -> castIsTotal f -> total (c ~~> f).
Proof. move => tc tf v. rewrite domCast/=. rewrite /castIsTotal in tf. specialize (tf v).
destruct (downcast f _) => //. apply tc. Qed.

Lemma totalSeq T U (c: Codec T) (d: Codec U) : total c -> total d -> total (c $ d).
Proof. move => totalc totald x. by rewrite domSeq /= totalc totald. Qed.

Lemma totalConstSeq T (c: Codec unit) (d: Codec T) : total c -> total d -> total (c .$ d).
Proof.  move => tc td x. apply totalCast => //. apply totalSeq => //. Qed.

(*======================================================================================
  Derivatives of codecs
  ======================================================================================*)
Fixpoint null t (c: Codec t) : Codec t :=
match c with
| Emp => Emp
| Alt _ c1 c2 => cAlt (null c1) (null c2)
| Seq _ _ c1 c2 => cSeq (null c1) (null c2)
| Cast _ _ f c => cCast (null c) f
| Star _ c => Cast (unNil _) Emp
| _ => Void _
end.

Fixpoint valIfNull t (c: Codec t) : option t :=
match c with
| Emp => Some tt
| Void _ => None
| Alt _ c1 c2 =>
  if valIfNull c1 is Some x then Some x else valIfNull c2
| Cast _ _ f c =>
  if valIfNull c is Some x then Some (upcast f x) else None
| Seq _ _ c1 c2 =>
  if valIfNull c1 is Some x1
  then if valIfNull c2 is Some x2
  then Some (x1,x2) else None else None
| Star _ c =>
  Some nil
| _ => None
end.

Fixpoint valsIfNull t (c: Codec t) : seq t :=
match c with
| Emp          => [::tt]
| Void _       => nil
| Alt _ c1 c2  => valsIfNull c1 ++ valsIfNull c2
| Cast _ _ f c  => [seq upcast f x | x <- valsIfNull c]
| Seq _ _ c1 c2 => [seq (x,y) | x <- valsIfNull c1, y <- valsIfNull c2]
| Star _ c => [::nil]
| _ => nil
end.

Fixpoint derivSym t (s: sym) (c: Codec t) : Codec t :=
match c with
| Any => Emp ~~> unConst s
| Sym s' => if s==s' then Emp  else Void _
| Alt _ c1 c2 => cAlt (derivSym s c1) (derivSym s c2)
| Seq _ _ c1 c2 => cAlt (cSeq (derivSym s c1) c2) (cSeq (null c1) (derivSym s c2))
| Cast _ _ f c => cCast (derivSym s c) f
| Star _ c => cSeq (derivSym s c) (Star c) ~~> unCons _
| _ => Void _
end.

Fixpoint interpAll t (r: Codec t) l xs :=
  if xs is x::xs then interp r l x /\ interpAll r l xs else True.

(* Only one direction *)
Lemma interpValIfNull t (r: Codec t) : forall x, valIfNull r = Some x -> interp r nil x.
Proof. induction r => x/=.
+ done.
+ done.
+ done.
+ done.
+ case E1: (valIfNull r1) => [x1 |] => //.
  case E2: (valIfNull r2) => [x2 |] => //.
  move => [<-]. exists nil, nil. split => //. split. by apply IHr1. by apply IHr2.
+ case E1: (valIfNull r1) => [x1 |]. move => [<-].
  have I1 := ((IHr1 _) E1). by left.
  move => H.
  have I2 := ((IHr2 _) H). by right.
+ by move => [<-].
+ move => H.
  case E: (valIfNull r) => [y |]; rewrite E in H => //.
  injection H => <-. exists y. split => //. by apply IHr.
Qed.

Lemma interpValIfNullConv t (r: Codec t) : forall x, interp r nil x -> exists y, valIfNull r = Some y.
Proof. induction r => x/=.
+ done.
+ done.
+ move => _. by exists tt.
+ done.
+ move => [l1 [l2 [H1 [H2 H3]]]]. destruct l1 => //. destruct l2 => //.
  destruct (IHr1 _ H2) as [y1 H4].
  destruct (IHr2 _ H3) as [y2 H5]. exists (y1,y2).
  by rewrite H4 H5.
+ elim => H. destruct (IHr1 _ H) as [y H1]. exists y. by rewrite H1.
  destruct (IHr2 _ H) as [y H1].
  case E: (valIfNull r1) => [z |]. by exists z. by exists y.
+ move => H. by exists nil.
+ move => [w [H1 H2]].
  destruct (IHr _ H2) as [z H3].
  exists (c z). by rewrite H3.
Qed.

Corollary interpValIfNullNone t (r: Codec t) x : valIfNull r = None -> interp r nil x -> False.
Proof.
move => H1 H2.
destruct (interpValIfNullConv H2) as [z H3].
by rewrite H1 in H3.
Qed.

Lemma interpNull t (r: Codec t) : forall l x, interp (null r) l x <-> (l = nil /\ interp r nil x).
Proof. induction r => l x; split => //.
+ move => [H1 H2]. done.
+ move => [H1 H2]. done.
+ intuition.
+ intuition.
+ move => /= H.
  rewrite -> cSeqSound in H. rewrite -> interpSeq in H.
  destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
  destruct (IHr1 l1 x.1) as [I1a I1b].
  destruct (IHr2 l2 x.2) as [I2a I2b].
  specialize (I1a H2). specialize (I2a H3).
  destruct I1a as [-> I1a]. destruct I2a as [-> I2a]. split => //.  exists nil, nil. intuition.
  move => [H1 [l1 [l2 [H2 [H3 H4]]]]].
  simpl. rewrite cSeqSound interpSeq. exists nil, nil. subst. split => //. destruct l1 => //. destruct l2 => //.
  split => //. apply IHr1; intuition.  apply IHr2; intuition.
+ move => /=H. rewrite -> cAltSound in H. rewrite -> interpAlt in H.
destruct H.
- specialize (IHr1 l x). destruct IHr1 as [I1 I2]. specialize (I1 H). intuition.
- specialize (IHr2 l x). destruct IHr2 as [I1 I2]. specialize (I1 H). intuition.
  move => [H1 H2]. subst.
  simpl. rewrite cAltSound interpAlt. destruct H2.
  specialize (IHr1 nil x). intuition.
  specialize (IHr2 nil x). intuition.
+ simpl. by move => [_ [-> ->]].
  move => [-> H]. exists tt. destruct x => //. simpl in H.
  destruct H as [s [l1 [l2 [H1 H2]]]].  done.
+ simpl. move => H1. rewrite -> cCastSound in H1. rewrite -> interpCast in H1.
destruct H1 as [w [H1 H2]]. subst.
destruct (IHr l w) as [I1 _]. specialize (I1 H2). destruct I1 as [-> I1].
split => //.  exists w. intuition.
move => [-> [w [H1 H2]]]. simpl. rewrite cCastSound. rewrite interpCast.
exists w. split => //. apply IHr. intuition.
Qed.

Lemma interpDerivSym c t (r:Codec t) : forall s x, interp (derivSym c r) s x <-> interp r (c::s) x.
Proof. admit. (* induction r => l x.
+ split => //= H. destruct H as [_ [H1 H2]]. by subst.
  injection H => [-> ->]. exists tt. intuition.
+ split => //= H.
  case E: (c == s). rewrite (eqP E). rewrite E in H. simpl in H. by subst.
  rewrite E in H. by simpl in H.
  injection H as [->]. rewrite eq_refl. simpl. congruence.
  simpl. split => //.
+ simpl. done.
+ simpl. rewrite cAltSound 2!cSeqSound. rewrite interpAlt 2!interpSeq.
  split => H.
  destruct H.
  - destruct H as [l1 [l2 [H1 [H2 H3]]]]. subst.
    exists (c::l1). exists l2. split => //. rewrite -> IHr1 in H2. intuition.
  - destruct H as [l1 [l2 [H1 [H2 H3]]]]. rewrite -> interpNull in H2.
    destruct H2 as [-> H2]. simpl in H1. subst. rewrite -> IHr2 in H3.
    exists nil. exists (c::l2). intuition.
  - destruct H as [l1 [l2 [H1 [H2 H3]]]].
    destruct l1.
    simpl in H1.  subst. right. exists nil, l. split => //.
    rewrite interpNull. intuition. by rewrite IHr2.
    left. simpl in H1. injection H1 => [H4 H5]. subst. exists l1, l2. split => //.
    rewrite IHr1. intuition.
+ simpl. rewrite cAltSound interpAlt.
  split => H.
  - destruct H. left. by apply IHr1.
    right. by apply IHr2.
  - destruct H. left. by apply IHr1.
    right. by apply IHr2.
+ simpl. split => H. destruct H as [[x' xs] [H1 H2]].
  rewrite -> cSeqSound in H2. rewrite -> interpSeq in H2.
  destruct H2 as [l1 [l2 [H3 [H4 H5]]]]. simpl in H4, H5. rewrite -> IHr in H4.
  subst. simpl. exists c, l1, l2. intuition.
  destruct x => //.
  simpl in H.
  destruct H as [s [l1 [l2 [H1 [H2 H3]]]]].
  injection H1 => [H4 H5]. subst. exists (t,x). split => //.
  rewrite cSeqSound. rewrite interpSeq. exists l1, l2. split => //. split.
  by rewrite IHr. done.
+ simpl. split => H.
  rewrite -> cCastSound in H. rewrite -> interpCast in H.
  destruct H as [w [H1 H2]].  subst. exists w. split => //. by rewrite -> IHr in H2.
  rewrite cCastSound. rewrite interpCast. destruct H as [w [H1 H2]].
  exists w. split => //. by rewrite IHr. *)
Qed.

(* Taking derivatives preserves determinism and prefix-free-ness *)
Lemma dpfInterpDerivSym t (c: Codec t) a : dpfInterp c -> dpfInterp (derivSym a c).
Proof. rewrite /dpfInterp => H l e v w. rewrite 2!interpDerivSym=> I1 I2. apply: H I1 I2. Qed.

(*======================================================================================
  Bit reader decoding of codecs

  We use derivatives "on-the-fly" to avoid any backtracking for deterministic codecs.
  ======================================================================================*)
(*
Require Import common.monad x86proved.bitreader.
Fixpoint codecToBitReader bits t (c: Codec t) : BitReader (option t) :=
  if valIfNull c is Some x then retn (Some x)
  else if bits isn't bits'.+1 then retn None
  else
    let! b = readBit;
    codecToBitReader bits' (derivSym b c).

(* Soundness of decoding *)
Lemma codecToBitReaderSound bits : forall t (c: Codec t) cursor cursor' l x rest,
  runBitReader (codecToBitReader bits c) cursor l = Some(cursor', rest, Some x) ->
  exists l', l = l' ++ rest /\ interp c l' x.
Proof. induction bits => t c cursor cursor' l x rest /= H //.
case E: (valIfNull c) => [y |]; rewrite E/= in H => //.
+ injection H => [<- <-] H'. exists nil. split => //. by apply interpValIfNull.
case E: (valIfNull c) => [y |]; rewrite E in H => //.
injection H => [<- ->] H'. have I:= interpValIfNull E. by exists nil.
destruct l => //. simpl in H.  destruct cursor => //.
simpl in H. destruct cursor => //. destruct (IHbits _ _ _ cursor' _ _ rest H) as [l' [-> H2]].
exists (b::l').
split => //. by apply interpDerivSym.
Qed.

(* Completeness of decoding: if a value is in the interpretation of a prefix-free codec, then
   codecToBitReader will return it *)
Require Import x86proved.bits.
Lemma codecToBitReaderComplete n  : forall t (c: Codec t) cursor cursor' l,
  dpfInterp c ->
  size l <= n ->
  apart (size l) cursor cursor' ->
  forall x, interp c l x ->
  forall rest, runBitReader (codecToBitReader n c) cursor (l ++ rest) = Some(cursor', rest, Some x).
Proof.
induction n => //.

+ move => t c cursor cursor' l DPF SIZE AP x I e. destruct l => //=.
  case E: (valIfNull c) => [y |].
- have J := interpValIfNull E. simpl in AP. subst.
  by elim (DPF _ _ _ _ I J) => [-> _].
- contradiction (interpValIfNullNone E I).

+ move => t c cursor cursor' l DPF SIZE AP x I e.
  destruct l => //.
  * (* l = nil *)
    simpl.
    case E: (valIfNull c) => [y |]. have J := (interpValIfNull E).
    simpl in AP. subst. elim (DPF _ _ _ _ I J) => [-> _]. done.
    contradiction (interpValIfNullNone E I).
+ specialize (IHn _ (derivSym s c)).
  have DPF': dpfInterp (derivSym s c) by apply dpfInterpDerivSym.
  simpl (size _) in AP. destruct cursor => //. simpl in AP.
  subst.
  specialize (IHn _ _ _ DPF' SIZE AP).
  simpl.
  case E: (valIfNull c) => [y |].
  - simpl. rewrite /dpfInterp in DPF.
    have HH := interpValIfNull E.
    rewrite /dpfInterp in DPF. specialize (DPF _ _ _ _ HH I). by destruct DPF.
  - simpl. apply IHn. by rewrite <-interpDerivSym in I.
Qed.

Corollary codecToFiniteBitReaderComplete t (c: Codec t) n cursor cursor' :
  dpfInterp c ->
  maxSize c = Some n ->
  forall l x, interp c l x ->
  apart (size l) cursor cursor' ->
  forall rest, runBitReader (codecToBitReader n c) cursor (l++rest) = Some(cursor', rest, Some x).
Proof.
move => DPF MAX l x I AP rest.
have SOUND := maxSizeSound MAX I.
eapply (codecToBitReaderComplete DPF SOUND AP I rest).
Qed.

Corollary codecToFiniteBitReaderRoundtrip t (c: Codec t) l e x n cursor cursor':
  dpfInterp c ->
  maxSize c = Some n ->
  apart (size l) cursor cursor' ->
  enc c x = Some l ->
  runBitReader (codecToBitReader n c) cursor (l ++ e) = Some(cursor', e, Some x).
Proof. move => DPF MAX AP ENC.
apply codecToFiniteBitReaderComplete => //. by apply encSound. Qed.

Example ex : Codec bool :=
    Sym false .$ Sym true  ~~> unConst false
||| Sym true  .$ Sym false ~~> unConst true.
*)
(*======================================================================================
  Executable decoder function; assume that all uses of Alt are non-ambiguous
  ======================================================================================*)

Inductive DecRes T :=
  DecYes (t: T) (rest: seq sym) | DecNo.

Definition castRes t u (f:CAST t u) (r: DecRes t) :=
  if r is DecYes v res then DecYes (upcast f v) res else DecNo _.

Fixpoint empRes t (c:Codec t) :DecRes t:=
  match c with
  | Emp => DecYes tt nil
  | Cast _ _ f c => if empRes c is DecYes v r then DecYes (upcast f v) r else DecNo _
  | _ => DecNo _
  end.

(* Not structurally recursive
Fixpoint decs t dec (l: seq sym) : DecRes (seq t) :=
  if l is s::l'
  then if dec l is DecYes x l' then if decs _ dec l' is DecYes xs l'' then DecYes (x::xs) l''
  else DecNo _ else DecNo _
  else DecYes nil nil.
*)

(* Note that dec actually does backtracking in Alt case *)
Implicit Arguments DecNo [T].

Fixpoint dec t (c: Codec t) (l: seq sym) : DecRes t :=
match c with
| Any       => if l is b::l then DecYes b l else DecNo
| Sym b     => if l is b'::l then if b==b'
               then DecYes tt l else DecNo else DecNo
| Emp       => DecYes tt l
| Void _    => DecNo
| Alt _ c d =>
  if dec c l is DecYes x l' then DecYes x l'
  else dec d l
| Seq _ _ c d =>
  if dec c l is DecYes x l'
  then if dec d l' is DecYes y l''
  then DecYes (x,y) l'' else DecNo else DecNo
| Cast _ _ f c =>
  if dec c l is DecYes x l'
  then DecYes (f x) l' else DecNo
| Star _ c =>
  DecNo
end.

(* Soundness applies regardless of determinism or prefix-free-ness *)
Lemma decSound t (c: Codec t) :
  forall l x rest, dec c l = DecYes x rest ->
  exists l', l = l' ++ rest /\ interp c l' x.
Proof. induction c => l x rest /= EQ.
(* Any *)
case E: l => [| x' xs]; rewrite E in EQ => //.
injection EQ => [-> ->]. by exists (x::nil).
(* Sym *)
case E: l => [| x' xs]; rewrite E in EQ => //.
case E': (s==x'); rewrite E' in EQ => //.
exists (x'::nil). rewrite (eqP E'). injection EQ => [<- H']. done.
(* Emp *)
exists nil. simpl. injection EQ => [] ->. done.
(* Void *)
done.
(* Seq *)
destruct x as [x1 x2].
case E1: (dec c1 l) => [x l' |]; rewrite E1 in EQ => //.
case E2: (dec c2 l') => [y l'' |]; rewrite E2 in EQ => //.
injection EQ => [<- <- <-].
destruct (IHc1 _ _ _ E1) as [l1 [-> H1]].
destruct (IHc2 _ _ _ E2) as [l2 [-> H2]].
exists (l1++l2). rewrite catA. split => //. simpl. by exists l1, l2.
(*(* Dep *)
case E1: (dec c l) => [x' l' | |]; rewrite E1 in EQ => //.
case E2: (dec (d x') l') => [y l'' | |]; rewrite E2 in EQ => //.
injection EQ => [<- <-].
destruct (IHc _ _ _ E1) as [l1 [-> H1]].
destruct (H _ _ _ _ E2) as [l2 [-> H2]].
exists (l1++l2). rewrite catA. split => //. exists l1, l2. split => //. *)
(* Alt *)
case E1: (dec c1 l) => [x' l' |]; rewrite E1 in EQ => //.
destruct (IHc1 _ _ _ E1) as [l1 [-> H1]].
exists l1. injection EQ => [-> <-]. split => //. by constructor.
destruct (IHc2 _ _ _ EQ) as [l2 [-> H2]]. exists l2. split => //. intuition.
(* Star *)
done.
(* Cast *)
case E1: (dec c0 l) => [x' l' |]; rewrite E1 in EQ => //.
destruct (IHc _ _ _ E1) as [l1 [-> H1]].
exists l1. injection EQ => [-> <-]. split => //. by exists x'.
Qed.

Lemma appeqpref t a: forall b c d: seq t, a++b = c++d ->
  (exists e, a=c++e /\ d=e++b) \/ (exists e, c=a++e /\ b=e++d).
Proof.
induction a => b c d /=EQ. subst. right. by exists c.
destruct c => //. left. simpl. exists (a::a0). intuition.
injection EQ => H1 H2. subst. specialize (IHa _ _ _ H1).
destruct IHa.
- destruct H as [e [E1 E2]]. subst. left. by exists e.
- destruct H as [e [E1 E2]]. subst. right. by exists e.
Qed.

(*
(* Dec is closed under extension of bytes *)
Lemma decExt t (c: Codec t) :
  forall l e,
  (forall x rest, dec c l = DecYes x rest -> dec c (l ++ e) = DecYes x (rest ++ e))
  /\
  (dec c l = DecNo _ -> dec c (l ++ e) = DecNo _).
Proof. induction c => l e; split => /=.
(* Any *)
move => x rest /= H.
case E: l => [| x' xs]; rewrite E in H => //.
injection H => [-> ->]. intuition.
destruct l => //=.
(* Sym *)
move => [] rest /= H.
case E: l => [| x' xs]; rewrite E in H => //.
case E': (s==x'); rewrite E' in H => //. rewrite (eqP E').
injection H => [<-]. by rewrite /= eq_refl.
destruct l => //=.
case E': (s==s0) => //.
(* Emp *)
move => [] rest /= H. by injection H => [->].
(* Void *)
done. done. done.
(* Seq *)
move => [x1 x2] rest /= H.
case E1: (dec c1 l) => [x l'| |]; rewrite E1 in H => //.
case E2: (dec c2 l') => [y l'' | |]; rewrite E2 in H => //.
injection H => [<- <- <-].
by rewrite (proj1 (IHc1 _ _) _ _ E1) (proj1 (IHc2 _ _) _  _ E2).
case E1: (dec c1 l) => [x l'| |] => //.
case E2: (dec c2 l') => [y l'' | |] => //.
rewrite (proj1 (IHc1 _ _) _ _ E1). by rewrite (proj2 (IHc2 _ _) E2).
by rewrite (proj2 (IHc1 _ _) E1).
(*(* Dep *)
move => v rest /= H'.
destruct v as [x w].
case E1: (dec c l) => [x' l'| |]; rewrite E1 in H' => //.
case E2: (dec (d x') l') => [y l'' | |]; rewrite E2 in H' => //.
injection H' => [<- <-] H''. subst.
rewrite (proj1 (IHc _ _) _ _ E1).
by rewrite (proj1 (H _ _ _) _  _ E2).
case E1: (dec c l) => [x l'| |] => //.
case E2: (dec (d x) l') => [y l'' | |] => //.
rewrite (proj1 (IHc _ _) _ _ E1). by rewrite (proj2 (H _ _ _) E2).
by rewrite (proj2 (IHc _ _) E1). *)
(* Alt *)
move => x rest /= H.
case E1: (dec c1 l) => [x' l' | |]; rewrite E1 in H => //.
rewrite (proj1 (IHc1 _ _) _ _ E1). by injection H => [-> <-].
rewrite (proj1 (IHc2 _ _) _ _ H). by rewrite (proj2 (IHc1 _ _) E1).
case E1: (dec c1 l) => [x' l' | |] => E2 //.
by rewrite (proj2 (IHc1 _ _) E1) (proj2 (IHc2 _ _) E2).
(* Cast *)
move => x rest /= H.
case E1: (dec c0 l) => [x' l' | |]; rewrite E1 in H => //.
rewrite (proj1 (IHc _ _) _ _ E1). by injection H => [-> <-].
case E1: (dec c0 l) => [x' l' | |] => E2 //.
by rewrite (proj2 (IHc _ _) E1).
Qed.

(* Note that the corresponding property does *not* hold of concatentation. e.g.
   (00|||0) $$ 1 is prefix-free but (00|0) is not.
*)
Lemma altDpf t (c d: Codec t): dpfInterp (Alt c d) -> dpfInterp c /\ dpfInterp d.
Proof.
rewrite /dpfInterp => H. split => l e v1 v2 I1 I2.
apply: (H l e v1 v2); by left.
apply: (H l e v1 v2); by right.
Qed.

*)

(*
Fixpoint ddec t (c: Codec t) (l: seq sym) : DecRes t :=
if l is b::l' then ddec (deriv b c) l'
else if null c is Emp then DecYes tt nil else DecNo _.
*)
