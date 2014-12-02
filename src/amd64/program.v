Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import bitsrep instr instrsyntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*=program *)
Inductive program :=
  prog_instr (c: Instr)
| prog_skip | prog_seq (p1 p2: program)
| prog_declabel (body: DWORD -> program)
| prog_label (l: DWORD).
(* | prog_data {T} {R: Reader T} {W: Writer T} (RT: Roundtrip R W) (v: T). *)
Coercion prog_instr: Instr >-> program.
(*=End *)

Require Import Ssreflect.tuple.

(* Instructions in instrsyntax are up to level 60, so delimiters need to be
   above that. *)
(*=programsyntax *)
Infix ";;" := prog_seq (at level 62, right associativity).
Notation "'LOCAL' l ';' p" := (prog_declabel (fun l => p))
  (at level 65, l ident, right associativity).
Notation "l ':;'" := (prog_label l)
  (at level 8, no associativity, format "l ':;'").
(*=End *)
Notation "l ':;;' p" := (prog_seq (prog_label l) p)
  (at level 8, p at level 65, right associativity,
   format "l ':;;'  p").