Add LoadPath "lf/".
Require Import numbers.

Theorem plus_n_0: forall n : nat, n = n + 0.

Proof.
  intros n.
  induction n as [| n' IHn' ].
    - reflexivity. (* n = 0 *)
    - simpl.
      rewrite <- IHn'.
      reflexivity.
  Qed.

(* Exercise *)
Theorem mult_0_r: forall n : nat, n * 0 = 0.

Proof.
  intros.
  induction n as [| n' IHn' ].
    - reflexivity. (* n = 0 *)
    - simpl.
      rewrite -> IHn'.
      reflexivity.
  Qed.

(* Exercise *)
Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + (S m).

Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
  Qed.

(* Exercise *)
Theorem plus_comm: forall n m : nat,
  n + m = m + n.

Proof.
  intros n m.
  induction n as [| n' IHn' ].
  - rewrite -> plus_0_n. rewrite <- plus_n_0. reflexivity.
  - simpl. rewrite -> IHn'. rewrite ->  plus_n_Sm. reflexivity.
  Qed.

(* Exercise *)
Theorem plus_assoc: forall n m p : nat,
  n + (m + p) = (n + m) + p.

Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed.

(* Exercise *)
Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n, double n = n + n.

Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
  Qed.

(* Exercise *)
Theorem even_S: forall n : nat,
  even (S n) = negb (even n).

Proof.
  intros.
  induction n as [| n' IHn' ].
  - simpl. reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity.
  Qed.
