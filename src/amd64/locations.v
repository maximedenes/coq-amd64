Require Import List PArith.
From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From OCamlBind Require Import ocamlbind reifiable.
Require Import reg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive loc :=
| R of gpReg
| S of nat.

Definition num_registers := 11.

Import Reifiable SExpr.

Definition export_gpReg r := Export (encode_gpReg r).

Definition error_gpReg := RBX.

Definition import_gpReg s :=
  if decode_gpReg (Import s) is Some x then x else error_gpReg.

Instance : Reifiable.t gpReg := Reifiable.New export_gpReg import_gpReg.

Definition export_loc l :=
  match l with
  | R n => B I (Export n)
  | S n => B (B I I) (Export n)
  end.

Definition error_loc := R error_gpReg.

Definition import_loc s :=
  match s with
  | B I v => R (Import v)
  | B (B I I) v => S (Import v)
  | _ => error_loc
  end.

Instance : Reifiable.t loc := Reifiable.New export_loc import_loc.