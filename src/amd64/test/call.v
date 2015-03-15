Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Example test1 : asm (CALL #x"5000000") = Some "E805000000". Time check. Qed.
Example test2 : asm (CALL RAX) = Some "FFD0". Time check. Qed.
Example test3 : asm (CALL [RAX]) = Some "FF10". Time check. Qed.        
