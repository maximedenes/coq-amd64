Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq Ssreflect.fintype.
Require Import bitsops bitsrep instr instrsyntax.

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

(* We define absolute jumps, calls and branches using labels *)
Definition relToAbs (c : DWORD -> Instr) : DWORD -> program :=
  fun a => LOCAL Next; c (subB a Next);; Next:;.

Definition JMP t := if t is JmpTgtI (mkTgt t) then relToAbs JMPrel t else JMPrel t.
Definition CALL t := if t is JmpTgtI (mkTgt t) then relToAbs CALLrel t else CALLrel t.
Definition JCC cc cv := relToAbs (JCCrel cc cv).

Arguments CALL (t)%ms.
Arguments JMP (t)%ms.

(*---------------------------------------------------------------------------
    Branch instructions
  ---------------------------------------------------------------------------*)
Notation "'JA'"  := (JCC CC_BE false) : instr_scope.
Notation "'JAE'" := (JCC CC_B  false) : instr_scope.
Notation "'JAB'" := (JCC CC_B  true)  : instr_scope.
Notation "'JBE'" := (JCC CC_BE true)  : instr_scope.
Notation "'JC'"  := (JCC CC_B  true)  : instr_scope.
Notation "'JE'"  := (JCC CC_Z true)   : instr_scope.
Notation "'JG'"  := (JCC CC_LE false) : instr_scope.
Notation "'JGE'" := (JCC CC_L false)  : instr_scope.
Notation "'JL'"  := (JCC CC_L true)   : instr_scope.
Notation "'JLE'" := (JCC CC_LE true)  : instr_scope.
Notation "'JNA'" := (JCC CC_BE true)  : instr_scope.
Notation "'JNB'" := (JCC CC_B false)  : instr_scope.
Notation "'JNBE'":= (JCC CC_BE false) : instr_scope.
Notation "'JNC'" := (JCC CC_B false)  : instr_scope.
Notation "'JNE'" := (JCC CC_Z false)  : instr_scope.
Notation "'JNG'" := (JCC CC_LE true)  : instr_scope.
Notation "'JNGE'":= (JCC CC_L true)   : instr_scope.
Notation "'JNL'" := (JCC CC_L false)  : instr_scope.
Notation "'JNLE'":= (JCC CC_LE false) : instr_scope.
Notation "'JNO'" := (JCC CC_O false)  : instr_scope.
Notation "'JNP'" := (JCC CC_P false)  : instr_scope.
Notation "'JNS'" := (JCC CC_S false)  : instr_scope.
Notation "'JNZ'" := (JCC CC_Z false)  : instr_scope.
Notation "'JO'"  := (JCC CC_O true)   : instr_scope.
Notation "'JP'"  := (JCC CC_P true)   : instr_scope.
Notation "'JPE'" := (JCC CC_P true)   : instr_scope.
Notation "'JPO'" := (JCC CC_P false)  : instr_scope.
Notation "'JS'"  := (JCC CC_S true)   : instr_scope.
Notation "'JZ'"  := (JCC CC_Z true)   : instr_scope.