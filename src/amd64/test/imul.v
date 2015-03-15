Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Example test1 : asm (IMUL RCX) = Some "48F7E9". Time check. Qed.
Example test2 : asm (IMUL [RCX]) = Some "48F729". Time check. Qed.
Example test3 : asm (IMUL RAX, RBX) = Some "480FAFC3". Time check. Qed.
Example test4 : asm (IMUL RAX, [RBX]) = Some "480FAF03". Time check. Qed.
Example test5 : asm (IMUL RAX, RBX, #x"12345689") = Some "4869C389563412". Time check. Qed.
Example test6 : asm (IMUL RAX, [RBX], #x"12345689") = Some "48690389563412". Time check. Qed.
