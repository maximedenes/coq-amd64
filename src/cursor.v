(*===========================================================================
    In order to formalize memory ranges, and reading the very last byte in
    memory, we introduce a type of Cursor, which is either an actual
    address or the address beyond the top of memory. In other words, this is
    just [0..2^n] where n is the number of bits in an address.
  ===========================================================================*)
From mathcomp Require Import all_ssreflect.
Require Import bitsrep bitsops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cursors.

(*=Cursor *)
Variable n:nat.
Inductive Cursor := mkCursor (p: BITS n) | top.
(*=End *)

(* Embedding into nat -- for proofs only! *)
Definition cursorToNat pos := if pos is mkCursor p then toNat p else 2^n.

(*---------------------------------------------------------------------------
    next: BITS n -> Cursor n
    and its properties
  ---------------------------------------------------------------------------*)
Definition next (p:BITS n) := if p == ones _ then top else mkCursor (incB p).

Definition nextCursor (p:Cursor) :=
  if p is mkCursor pos then next pos else top.

(*---------------------------------------------------------------------------
    Order relations on Cursor
  ---------------------------------------------------------------------------*)
Definition ltCursor (pos1 pos2: Cursor) :=
  match pos1, pos2 with
  | top, _ => false
  | mkCursor p1, mkCursor p2 => ltB p1 p2
  | mkCursor _, top => true
  end.
Definition leCursor (pos1 pos2: Cursor) :=
  match pos1, pos2 with
  | _, top => true
  | top, mkCursor _ => false
  | mkCursor p1, mkCursor p2 => leB p1 p2
  end.

Fixpoint nexts k (c: Cursor) : option (Cursor) :=
  match k , c with
  | 0 , _ => Some c
  | k'.+1 , mkCursor p => nexts k' (next p)
  | k'.+1 , top => None
  end.

(*---------------------------------------------------------------------------
    Apart by n
  ---------------------------------------------------------------------------*)
Fixpoint apart n (p q: Cursor) :=
  match n, p with
  | n'.+1, mkCursor p' => apart n' (next p') q (* q = next (p' +# n)  *)
  | 0, _ => q = p
  | _, _ => False
  end.

(*---------------------------------------------------------------------------
    Subtraction
  ---------------------------------------------------------------------------*)
Definition subCursor (p q: Cursor) : Cursor :=
  match p, q with
  | _, top => mkCursor (zero _)
  | mkCursor p', mkCursor q' =>
    if leB p' q' then mkCursor (zero _) else mkCursor (subB p' q')
  | top, mkCursor p' =>
    if p' == zero _ then top else mkCursor (negB p')
  end.

(*---------------------------------------------------------------------------
    Range testing
  ---------------------------------------------------------------------------*)
Definition inRange p q := fun p' => leCursor p p' && ltCursor p' q.
Definition outRange p q := fun p' => ltCursor p' p && leCursor q p'.

End Cursors.

Coercion mkCursor : BITS >-> Cursor.

(** Convenience definitions for various sizes of cursor *)
(*Definition NIBBLECursor := Cursor n4.
Definition BYTECursor   := Cursor n8.
Definition WORDCursor   := Cursor n16.*)
Definition DWORDCursor  := Cursor n32.
(*Definition QWORDCursor  := Cursor n64.
Definition DWORDorBYTECursor (d: bool) := Cursor (if d then n32 else n8).*)

(*Coercion mkNIBBLECursor (x: NIBBLE) : NIBBLECursor := mkCursor x.
Coercion mkBYTECursor   (x: BYTE)   : BYTECursor   := mkCursor x.
Coercion mkWORDCursor   (x: WORD)   : WORDCursor   := mkCursor x.
Coercion mkDWORDCursor  (x: DWORD)  : DWORDCursor  := mkCursor x.
Coercion mkQWORDCursor  (x: QWORD)  : QWORDCursor  := mkCursor x.
Coercion mkDWORDorBYTECursor d (x: DWORDorBYTE d) : DWORDorBYTECursor d := mkCursor x.*)

Identity Coercion DWORDCursortoCursor32 : DWORDCursor >-> Cursor.

Definition widenCursor n1 n2 (c: Cursor n1) : Cursor (n2+n1) :=
  if c is mkCursor p then mkCursor (p ## zero n2) else top _.

(* Because Cursor is essentially isomorphic to option, we can inherit
   many canonical structures. *)
Section CursorCanonicals.
  Variable n: nat.

  Definition cursor_option (p: Cursor n) : option (BITS n) :=
    if p is mkCursor p' then Some p' else None.

  Definition option_cursor (o: option (BITS n)) : Cursor n :=
    if o is Some p' then mkCursor p' else top n.

  Lemma cursor_optionC: cancel cursor_option option_cursor.
  Proof. by move=> [p|] /=. Qed.

  Definition Cursor_eqMixin := CanEqMixin cursor_optionC.
  Canonical Structure Cursor_eqType :=
    Eval hnf in EqType (Cursor n) Cursor_eqMixin.

  Definition Cursor_countMixin := CanCountMixin cursor_optionC.
  Definition Cursor_choiceMixin := CountChoiceMixin Cursor_countMixin.
  Canonical Structure Cursor_choiceType :=
    Eval hnf in ChoiceType _ Cursor_choiceMixin.
  Canonical Structure Cursor_countType :=
    Eval hnf in CountType _ Cursor_countMixin.

  Definition Cursor_finMixin := Eval hnf in CanFinMixin cursor_optionC.
  Canonical Structure Cursor_finType := Eval hnf in FinType _ Cursor_finMixin.
End CursorCanonicals.