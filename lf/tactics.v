Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/".
Require Import numbers.
Require Import lists.
Require Import poly.
Require Import List.
Import ListNotations.

Theorem silly1: forall (n m o p : nat),
  n = m ->
  [n;o] = [n;p] ->
  [n;o] = [m;p].

Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* instead of: rewrite -> eq2. reflexivity. *)
  apply eq2. Qed.

Theorem silly2: forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].

Proof.
  intros m n o p eq1 eq2.
  apply eq2. apply eq1.
  Qed.

Theorem silly2a: forall (n m : nat),
  (n, n) = (m, m) ->
  (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].

Proof.
  intros n m eq1 eq2.
  (* apply eq2 instantiates q to n, r to m *)
  apply eq2. apply eq1.
  Qed.

(* Exercise *)
Theorem silly_ex:
  (forall n, even n = true -> odd (S n) = true) ->
    odd 3 = true ->
    even 4 = true.

Proof.
  intros eq1 eq2.
  apply eq2.
  Qed.

(* conclusion and goal must line up for `apply` *)
(* here, we use `symmetry` to switch lhs/rhs *)
Theorem silly3: forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.

Proof.
  intros n H.
  symmetry.
  apply H. Qed.

(* Exercise *)
Lemma rev_injective: forall m n : list nat,
  rev m = rev n -> m = n.

Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
  Qed.

Theorem rev_exercise_1: forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.

Proof.
  intros l l' H.
  apply rev_injective.
  symmetry.
  rewrite rev_involutive.
  apply H.
  Qed.

(* Demonstrating `apply ... with` *)
Example trans_eq_example:
  forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
  Qed.

(* The above has 2 rewrites, and is a common pattern *)
(* which can be expressed as *)
Theorem trans_eq: forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.

Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
  Qed.

Example trans_eq_example':
  forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2. Qed.

(* Exercise *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Example trans_eq_exercise: forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).

Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m := minustwo o).
  - rewrite -> eq2. apply eq1.
  - reflexivity.
  Qed.
