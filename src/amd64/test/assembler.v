Require Import String.
From Ssreflect 
     Require Import ssreflect eqtype seq tuple.
Require Import bitsrep codec.
From amd64 
     Require Import instr instrcodec.

Fixpoint toHex (bs: list bool): string :=
  match bs with
  | [::] => EmptyString
  | [:: x] => appendNibbleOnString (zero 3 ## [tuple x]) EmptyString
  | [:: x; y] => appendNibbleOnString (zero 2 ## [tuple x; y]) EmptyString
  | [:: x; y; z] => appendNibbleOnString (zero 1 ## [tuple x; y; z]) EmptyString
  | [:: a, b, c, d & bs] => appendNibbleOnString [tuple a; b; c; d] (toHex bs)
  end.

Definition asm (instr: Instr): option string :=
  if enc InstrCodec instr is Some bs then Some (toHex bs)
  else None.
