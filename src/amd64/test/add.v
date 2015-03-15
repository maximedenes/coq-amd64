Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

(* TODO: fix coercion, remove manual tweak *)
Example test1 : asm (ADD RAX, (#x"12345678":DWORD)) = Some "480578563412". Time check. Qed.
Example test2 : asm (ADD RBX, (#x"12345678":DWORD)) = Some "4881C378563412". Time check. Qed.
Example test3 : asm (ADD RCX, (#x"12345678":DWORD)) = Some "4881C178563412". Time check. Qed.
Example test4 : asm (ADD RAX, RBX) = Some "4801D8". Time check. Qed.
Example test5 : asm (ADD [RAX], RBX) = Some "480118". Time check. Qed.
Example test5 : asm (ADD RAX, [RAX]) = Some "480300". Time check. Qed.
