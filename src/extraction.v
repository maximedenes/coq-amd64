Require Import List Arith ZArith.
From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From CoqFFI Require Import coqFFI reifiable.
From Amd64 Require Import bitsrep amd64.instr amd64.program amd64.reification.

Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Cd "extraction".

Extraction Blacklist List String Int.

Separate Extraction bitsrep.toZ reg instr program reification.

Cd "..".
