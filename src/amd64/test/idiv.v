Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Example test1 : asm (IDIV RAX) = Some "48F7F8". Time check. Qed.
Example test2 : asm (IDIV [RAX]) = Some "48F738". Time check. Qed.
        
        
