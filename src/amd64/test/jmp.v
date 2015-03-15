Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Definition backward := #x"FFFFFFF9".
Definition forward := #x"000000b5".

Example test1 : asm (JMP backward) = Some "". Time check. Qed.
Example test2 : asm (JMP forward) = Some "". Time check. Qed.
Example test3 : asm (JMP RAX) = Some "". Time check. Qed.
Example test4 : asm (JMP [RAX]) = Some "". Time check. Qed.
