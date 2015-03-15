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

Example test1 : asm (JO backward) = Some "0F80F9FFFFFF". Time check. Qed.
Example test2 : asm (JO forward) = Some "0F80b5000000". Time check. Qed.
Example test3 : asm (JNO backward) = Some "0F81EDFFFFFF". Time check. Qed.
Example test4 : asm (JNO forward) = Some "0F81A9000000". Time check. Qed.
Example test5 : asm (JC backward) = Some "0F82E1FFFFFF". Time check. Qed.
Example test6 : asm (JC forward) = Some "0F829D000000". Time check. Qed.
Example test7 : asm (JNC backward) = Some "0F83D5FFFFFF". Time check. Qed.
Example test8 : asm (JNC forward) = Some "0F8391000000". Time check. Qed.
Example test9 : asm (JZ backward) = Some "0F84C9FFFFFF". Time check. Qed.
Example test10 : asm (JZ forward) = Some "0F8485000000". Time check. Qed.
Example test11 : asm (JNZ backward) = Some "0F85BDFFFFFF". Time check. Qed.
Example test12 : asm (JNZ forward) = Some "0F8579000000". Time check. Qed.
Example test13 : asm (JNA backward) = Some "0F86B1FFFFFF". Time check. Qed.
Example test14 : asm (JNA forward) = Some "0F866D000000". Time check. Qed.
Example test15 : asm (JA backward) = Some "0F87A5FFFFFF". Time check. Qed.
Example test16 : asm (JA forward) = Some "0F8761000000". Time check. Qed.
Example test17 : asm (JS backward) = Some "0F8899FFFFFF". Time check. Qed.
Example test18 : asm (JS forward) = Some "0F8855000000". Time check. Qed.
Example test19 : asm (JNS backward) = Some "0F898DFFFFFF". Time check. Qed.
Example test20 : asm (JNS forward) = Some "0F8949000000". Time check. Qed.
Example test21 : asm (JP backward) = Some "0F8A81FFFFFF". Time check. Qed.
Example test22 : asm (JP forward) = Some "0F8A3D000000". Time check. Qed.
Example test23 : asm (JNP backward) = Some "0F8B75FFFFFF". Time check. Qed.
Example test24 : asm (JNP forward) = Some "0F8B31000000". Time check. Qed.
Example test25 : asm (JNL backward) = Some "0F8C69FFFFFF". Time check. Qed.
Example test26 : asm (JNL forward) = Some "0F8C25000000". Time check. Qed.
Example test27 : asm (JNG backward) = Some "0F8E51FFFFFF". Time check. Qed.
Example test28 : asm (JNG forward) = Some "0F8E0D000000". Time check. Qed.
Example test29 : asm (JG backward) = Some "0F8F45FFFFFF". Time check. Qed.
Example test30 : asm (JG forward) = Some "0F8F01000000". Time check. Qed.
