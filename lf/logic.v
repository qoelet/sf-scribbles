Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/".
Require Import numbers.
Require Import induction.
Require Import poly.
Require Import tactics.

(* Propositions are first class objects in Coq *)
Theorem plus_2_2_is_4:
  2 + 2 = 4.

Proof. reflexivity. Qed.

Definition plus_fact: Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true:
  plus_fact.

Proof. reflexivity. Qed.

(* Props can be parametrized *)
Definition is_three (n : nat) : Prop :=
  n = 3.

Check is_three 3. (* is_three defines properties of their arguments *)

Definition injective {A B} (f: A -> B) :=
  forall x y : A,
  f x = f y ->
  x = y.

Lemma succ_inj : injective S.

Proof.
  intros n m H.
  inversion H.
  reflexivity.
  Qed.

Check @eq.

(* Logical connectives *)
Example and_example:
  3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  split.
  - reflexivity.
  - reflexivity.
  Qed.

Lemma and_intro:
  forall A B: Prop,
  A -> B ->
  A /\ B.

Proof.
  intros A B HA HB.
  split.
  - apply HA.
  - apply HB.
  Qed.

Example and_example':
  3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
  Qed.

(* Exercise *)
Example and_exercise:
  forall n m : nat,
  n + m = 0 ->
  n = 0 /\ m = 0.

Proof.
  intros n m.
  split.
  generalize dependent m.
  - intros m. induction m as [| m' ].
    + intro H.
      rewrite plus_comm in H.
      rewrite plus_0_n in H.
      apply H.
    + destruct n.
      * simpl. intro H. reflexivity.
      * simpl. intro H. inversion H.
  - induction m as [| m' ].
    + reflexivity.
    + destruct n.
      * simpl in H. inversion H.
      * simpl in H. inversion H.
  Qed.
