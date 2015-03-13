Require Import String.
From Ssreflect
     Require Import ssreflect ssrnat.
Require Import bitsrep.
From amd64 
     Require Import reg instr instrsyntax test.assembler.

Open Scope memspec_scope.
Open Scope instr_scope.
Open Scope string.

Example test1 : asm (MOV AL, BL) = Some "88d8". check. Qed.

(* TODO: support access to upper half *)
(* Definition ex2 := MOV AH, BL. *)

Example test3 : asm (MOV [RAX], AL) = Some "8800". check. Qed.
Example test4 : asm (MOV RAX, RBX) = Some "4889d8". check. Qed.
Example test5 : asm (MOV [RAX], RBX) = Some "488918". check. Qed.
Example test6 : asm (MOV AL, [RAX]) = Some "8a00". check. Qed.
Example test7 : asm (MOV RAX,[RAX]) = Some "488b00". check. Qed.
Example test8 : asm (MOV R8,[RAX]) = Some "4c8b00". check. Qed.
Example test9 : asm (MOV RAX,[R8]) = Some "498b00". check. Qed.

(* TODO: generalize InstrSrc to any constant size *)
(*
Definition ex10 := MOV AL, #x"42".
 *)

(* TODO: fix cast issue between BITS 64 and QWORD *)
Example test11 : asm (MOV RBX, (#x"123456789ABCDEF0": QWORD)) = Some "48bbf0debc9a78563412". check. Qed.
Example test12 : asm (MOV R11, (#x"123456789ABCDEF0": QWORD)) = Some "49bbf0debc9a78563412". check. Qed. 
Example test13 : asm (MOV RAX, [RIP + #x"12345678"]) = Some "488b0578563412". check. Qed.



