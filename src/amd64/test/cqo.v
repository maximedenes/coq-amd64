Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Example test1 : asm CQO = Some "4899". Time check. Qed.

