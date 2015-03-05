Require Import List Arith ZArith.
From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From OCamlBind Require Import ocamlbind reifiable.
From Amd64 Require Import bitsrep amd64.instr amd64.instrcodec amd64.program.

Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlString.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Cd "extraction".

Extraction Blacklist List String Int.

Separate Extraction bitsrep.toZ reg instr program.

Cd "..".
