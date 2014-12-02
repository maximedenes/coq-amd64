Require Import ZArith.
From Ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
Require Import bitsrep bitsops reg instr instrsyntax program.
Require Import monadic locations errors.

Open Scope Z_scope.
Open Scope instr_scope.
Open Scope string_scope.
Open Scope error_monad_scope.

Import Monadic.

(*
Definition decoder r :=
   if decode_gpReg r is Some r then OK r else Error (msg "decoder").
*)

Definition stk (s : nat) := [RSP + (s * 8)%N]%ms.

Definition loc l : InstrSrc :=
  match l with
  | R r => r
  | S s => stk s
  end.

(* TODO: switch to Compcert's integers *)

Definition max_int32 := toZ #x"3fffffff".
Definition min_int32 := - (toZ #x"40000000").

Definition encode_int s n : BITS s := orB (shlB (fromZ n)) #1.

Definition small_int n := (n <=? max_int32) && (n >=? min_int32).

Definition alloc_stackframe num_slots k :=
  if (num_slots > 0)%N then
  SUB [RSP], num_slots;; k else k.

Definition free_stackframe num_slots k :=
  if (num_slots > 0)%N then
  ADD [RSP], num_slots;; k else k.

(* Evaluate an atom, leaving its value in the given register. *)
Fixpoint atom2reg a dst k :=
  match a with
  | Var (R r) =>
    if r != dst then OK (MOV dst, r;; k) else OK k
  | Var (S s) => OK (MOV dst, stk s;; k)
  | Constant (Int n) =>
    if small_int n then
      OK (MOV dst, (encode_int n32 n : DWORD);; k)
    else
      OK (MOVABS dst (encode_int n64 n);; k)
  | Constant (Symbol s) =>
    (* FIXME: treat labels properly *)
    OK (LEA dst, [RIP + Pos.to_nat (Ident.uid s)];; k)
       (*
  | Constant c => LEA dst, [RIP + ]
*)
  | Field n (Var (R r)) =>
    OK (MOV dst, [r + (n * 8)%N];; k)
  | Field n (Constant (Symbol s)) =>
    (* FIXME: treat labels properly *)
    OK (MOV dst, [RIP + (Pos.to_nat (Ident.uid s) + n * 8)%N];; k)
  | Field n a1 =>
    let k := MOV dst, [dst + (n * 8)%N];; k in
    atom2reg a1 dst k
  | _ => Error (msg "atom2reg")
  end.

(* Evaluate an atom, leaving its value in some register.
   Can destroy rax.  Return the register containing the value *)

Definition atom2somereg a k :=
  if a is Var (R r) then OK (k r) else atom2reg a RAX (k RAX).

Definition atoms2someregs a1 a2 k :=
  match a1, a2 with
  | Var (R r1), Var (R r2) => OK (k r1 r2)
  | Var (R r), _ => atom2reg a2 RAX (k r RAX)
  | _, Var (R r) => atom2reg a1 RAX (k RAX r)
  | _, _ => do k <- atom2reg a2 RDX (k RAX RDX); atom2reg a1 RAX k
  end.

(* Evaluate an atom and store its value at the given location (reg + offset).
   Can destroy rax.  The destination reg must not be rax. *)

Definition atom2mem a idx ofs k :=
  match a with
  | Var (R r) => OK (MOV [idx + ofs], r;; k)
  | Constant (Int n) =>
    if small_int n then OK (MOV [idx + ofs], (encode_int n32 n : DWORD);; k)
    else atom2reg a RAX k
  | _ => atom2reg a RAX k
  end.

(* Evaluate an atom, storing its value in the given location *)
(* Can destroy rax *)

Definition atom2loc a dst k :=
  match dst with
  | R r => atom2reg a r k
  | S s => atom2mem a RSP (8 * s)%N k
  end.

(* Print a simple atom.  A simple atom is one that corresponds to an
   x86 reg-or-mem-or-const operand. *)

Definition simple_atom a : res InstrSrc :=
  match a with
  | Var n => OK (loc n)
  | Constant (Int n) =>
    if small_int n then OK (ConstSrc (encode_int n32 n))
    else Error (msg "simple_atom")
  | Field n (Var (R r)) =>
    OK ([r + (8 * n)%N]%ms : InstrSrc)
  | _ => Error (msg "simple_atom")
  end.

(* Reduce an atom to a simple atom, emitting some code if needed.
   Can destroy rdx.  Return the simple atom that completes the computation. *)

Definition atom2simple a k :=
  match a with
  | Var l => do a <- simple_atom a; OK (k a)
  | Constant (Int n) =>
    if small_int n then do a <- simple_atom a; OK (k a) else
    do a' <- simple_atom (Var (R RDX)); atom2reg a RDX (k a')
  | Field n (Var (R r)) => do a <- simple_atom a; OK (k a)
  | Field n a => do a' <- simple_atom (Field n (Var (R RDX)));
                 atom2reg a RDX (k a')
  | _ => do a' <- simple_atom (Var (R RDX)); atom2reg a RDX (k a')
  end.

(* Arithmetic *)

(* 2(-a) + 1 = 2 - (2a + 1) *)

Definition intneg a dst k :=
  let k a :=
    MOV   RAX, 2%N;;
    SUB   RAX, a;;
    MOV   dst, RAX;;
    k
  in atom2simple a k.

(* 2(a + b) + 1 = (2a + 1) + 2b *)

Definition intadd_imm a n dst k :=
  if (n =? 0)%Z then atom2loc a dst k else
    let n2 := n * 2 in
    match dst with
    | R rd =>
      let k r1 :=
        LEA rd, [r1 + n2];; k
      in atom2somereg a k
    | S sd =>
      let k :=
        ADD RAX, n2;;
        MOV (stk sd), RAX;;
        k
      in
      atom2reg a RAX k
  end.

(* 2(a + b) + 1 = (2a + 1) + (2b + 1) - 1 *)

Definition intadd_aux a1 a2 dst k :=
  match dst with
  | R rd =>
    let k a1 a2 :=
      LEA rd, [a1 + a2 - 1%N]%ms;;
      k
    in atoms2someregs a1 a2 k
  | S sd =>
    let k a2 :=
      ADD   RAX, a2;;
      SUB   RAX, 1%N;;
      MOV   (stk sd), RAX;;
      k
    in
    do k <- atom2simple a2 k;
    atom2reg a1 RAX k
  end.

Definition intadd a1 a2 dst k :=
  match a1, a2 with
  | Constant (Int n1), _ =>
    if small_int n1 then intadd_imm a2 n1 dst k
    else intadd_aux a1 a2 dst k
  | _, Constant (Int n2) =>
    if small_int n2 then intadd_imm a1 n2 dst k
    else intadd_aux a1 a2 dst k
  | _, _ => intadd_aux a1 a2 dst k
  end.

(* 2(a - b) + 1 = (2a + 1) - (2b + 1) + 1 *)

Definition intsub_aux a1 a2 dst k :=
  match dst with
  | R rd =>
    let k a2 :=
      SUB   RAX, a2;;
      LEA   rd, [RAX + 1%N];;
      k
    in
    do k <- atom2simple a2 k;
    atom2reg a1 RAX k
  | S sd =>
    let k a2 :=
      SUB   RAX, a2;;
      ADD   RAX, 1%N;;
      MOV   (stk sd), RAX;;
      k
    in
    do k <- atom2simple a2 k;
    atom2reg a1 RAX k
  end.

Definition intsub a1 a2 dst k :=
  match a2 with
  | Constant (Int n2) => if small_int (-n2) then intadd_imm a1 (-n2) dst k
                         else intsub_aux a1 a2 dst k
  | _ => intsub_aux a1 a2 dst k
  end.

(* powers of two -> shift ? *)
(* 2(a * b) + 1 = (2a + 1) * b + (1 - b) *)

Definition intmul_imm a (n : Z) dst k :=
  match dst with
  | R rd =>
      let k :=
        IMUL   RAX, RAX, n;;
        LEA    rd, [RAX + (1-n)];;
        k
      in
      atom2reg a RAX k
  | S sd =>
      let k :=
        IMUL   RAX, n;;
        SUB    RAX, n-1;;
        MOV    (stk sd), RAX;;
        k
      in
      atom2reg a RAX k
  end.