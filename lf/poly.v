(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/"
Require Import lists.

(* Polymorphic lists *)
Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count')
  end.

Example test_repeat_1:
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Proof.
  reflexivity. Qed.

Example test_repeat_2:
  repeat bool false 1 = cons bool false (nil bool).

Proof.
  reflexivity. Qed.

(* Exercise *)
Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.

End MumbleGrumble.
