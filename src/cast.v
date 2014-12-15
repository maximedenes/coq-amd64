From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*======================================================================================
  We define a type of "casts".
  - Mathematically, this consists of a partial function [downcast] and a left inverse
    [upcast], together with the defining property [castinv].
  - For our purposes, [upcast] corresponds to *decoding*, and is not necessarily
    injective (values may have more than one code), and [downcast] corresponds to
    *encoding*, which may fail, and is not unique (it just *picks* some code).
  ======================================================================================*)
Structure CAST t u := MakeCast
{ upcast: t -> u;
  downcast: u -> option t;
  castinv : forall x y, downcast x = Some y -> upcast y = x
}.
Implicit Arguments MakeCast [t u].

Coercion upcast : CAST >-> Funclass.

Definition castIsTotal t u (c: CAST t u) := forall x, isSome (downcast c x).

(* Identity cast and composition of casts *)
Definition idCast t : CAST t t.
apply: MakeCast (fun x => x) (fun x => Some x) _.
by move => ? ? [->].
Defined.

Definition composeCast t u v (c: CAST t u) (d: CAST u v) : CAST t v.
Proof.
apply: MakeCast (fun x => upcast d (upcast c x))
                (fun x => if downcast d x is Some x' then downcast c x' else None) _.
move => x y.
case E: (downcast d x) => [x' |] //= E'. by rewrite (castinv E') (castinv E).
Defined.

(* Constructor casts *)
Definition unNil t : CAST unit (seq t).
apply: MakeCast (fun _ => nil) (fun x => if x is nil then Some tt else None) _. elim => //.
Defined.

Definition unCons t : CAST (t * seq t) (seq t).
apply: MakeCast (fun p => (p.1) :: (p.2)) (fun x => if x is x::xs' then Some (x,xs') else None) _.
elim => //. move => x xs H. move => [x' xs']. by move => [-> ->].
Defined.

Definition unInl t u : CAST t (t+u).
apply: MakeCast (fun x => inl x) (fun x => if x is inl y then Some y else None) _.
elim => x y => //. by move => [->]. Defined.

Definition unInr t u : CAST u (t+u).
apply: MakeCast (fun x => inr x) (fun x => if x is inr y then Some y else None) _.
elim => x y => //. by move => [->]. Defined.

Definition unConst (t: eqType) (x:t) : CAST unit t.
apply: MakeCast (fun _ => x) (fun x' => if x == x' then Some tt else None) _.
move => x1 x2. case E: (_==_) => //. by rewrite (eqP E).
Defined.

(* Projection casts *)
Definition fstCast t u (y:u) : CAST (t*u) t.
apply: MakeCast (fun x => x.1) (fun x => Some (x,y)) _. by move => x0 [x y'] [<-]. Defined.

Definition sndCast t u (x:t) : CAST (t*u) u.
apply: MakeCast (fun x => x.2) (fun y => Some (x,y)) _. by move => x0 [x' y] [<-]. Defined.

Definition unitCast t : CAST t unit.
apply: MakeCast (fun _ => tt) (fun _ => None) _. by move => []. Defined.

(* Isomorphisms as casts *)
Definition unitRcast t : CAST t (t*unit).
apply: MakeCast (fun x => (x,tt)) (fun x => Some x.1) _.
by move => [x []] x' [->].
Defined.

Definition unitLcast t : CAST t (unit*t).
apply: MakeCast (fun x => (tt,x)) (fun x => Some x.2) _.
by move => [[] x] x' [->].
Defined.

Definition fstUnitCast t : CAST (t*unit) t.
apply: MakeCast (fun x => x.1) (fun x => Some (x,tt)) _.
by move => x [y []] [->]. Defined.

Definition sndUnitCast t : CAST (unit*t) t.
apply: MakeCast (fun x => x.2) (fun x => Some (tt,x)) _.
by move => x [[] y] [->]. Defined.

Definition existTcast T U : CAST {_:T & U} (T*U).
apply: MakeCast (fun (p: {_:T & U}) => (projT1 p, projT2 p))
                (fun x => Some (existT (fun _ => U) x.1 x.2)) _.
by move => [y z] [y' z'] [->]  ->.
Defined.

Definition sumCast F : CAST (F false + F true) {x:bool & F x}.
apply: (MakeCast (fun (p: F false + F true) =>
                 match p with inl x => existT _ false x | inr x => existT _ true x end)
                (fun (p: {x:bool & F x}) =>
                 Some (match p with
                 | existT false x => inl x
                 | existT true x => inr x end)) _).
elim => [x y]. elim => [a | b] => H; destruct x; congruence. Defined.

Definition pairAssocCast t1 t2 t3 : CAST (t1*(t2*t3)) ((t1*t2)*t3).
apply: MakeCast (fun (x: t1*(t2*t3)) => ((x.1,x.2.1),x.2.2))
                (fun (x: (t1*t2)*t3) => Some (x.1.1, (x.1.2, x.2))) _.
move => [[x1 x2] x3] [y1 [y2 y3]]. by move => [-> -> -> ].
Defined.

Definition pairAssocCastOp t1 t2 t3 : CAST ((t1*t2)*t3) (t1*(t2*t3)).
apply: MakeCast (fun (x: (t1*t2)*t3) => (x.1.1, (x.1.2, x.2))) 
                (fun (x: t1*(t2*t3)) => Some ((x.1,x.2.1),x.2.2))
                _.
move => [x1 [x2 x3]] [[y1 y2] y3]. by move => [-> -> -> ].
Defined.

Definition swapPairCast t u : CAST (t*u) (u*t).
apply: MakeCast (fun (x:t*u) => (x.2,x.1)) (fun (x:u*t) => Some (x.2,x.1)) _.
by move => [x1 x2] [y1 y2] [-> ->].
Defined.

(* Congruences *)
Definition pairOfCasts t t' u u' (c: CAST t t') (d: CAST u u') : CAST (t*u) (t'*u').
apply: MakeCast (fun x => (upcast c x.1,upcast d x.2))
                (fun x => match downcast c x.1, downcast d x.2 with
                            Some y, Some z => Some (y,z) | _, _ => None end) _.
move => [x1 x2] [y1 y2]/=.
case E: (downcast c x1) => [y1' |]//.
case E': (downcast d x2) => [y2' |]//. move => [<- <-].
by rewrite (castinv E) (castinv E').
Defined.

Definition sumOfCasts t t' u u' (c: CAST t t') (d: CAST u u') : CAST (t+u) (t'+u').
apply: MakeCast (fun x => match x with inl y => inl (c y) | inr z => inr (d z) end)
                (fun x => match x with
                 | inl y => if downcast c y is Some z then Some (inl z) else None
                 | inr y => if downcast d y is Some z then Some (inr z) else None end) _.
elim => [y | y]. elim => [z | z].
case E: (downcast c y) => [x |]//. move => [<-]. by rewrite (castinv E).
case E: (downcast c y) => [x |]//.
elim => [z | z].
case E: (downcast d y) => [x |]//.
case E: (downcast d y) => [x |]//. move => [<-]. by rewrite (castinv E).
Defined.
