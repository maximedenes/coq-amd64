(*===========================================================================
    Some useful instances of Monad
  ===========================================================================*)
From mathcomp Require Import all_ssreflect.
Require Import monad.
Require Import Coq.Lists.Streams.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Logic.FunctionalExtensionality.

(*---------------------------------------------------------------------------
    Option monad
  ---------------------------------------------------------------------------*)
Instance optionMonadOps : MonadOps option :=
{ retn := Some
; bind := fun X Y (c: option X) f => if c is Some y then f y else None }.

Instance optionMonad : Monad option.
Proof. apply Build_Monad. done. move => X; by case. move => X Y Z; by case. Qed.