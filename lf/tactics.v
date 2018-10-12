Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/".
Require Import numbers.
Require Import induction.
Require Import lists.
Require Import poly.
Require Import List.
Require Import Coq.Arith.Mult.
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

(* Demonstrating `inversion` *)
Theorem S_injective: forall (n m : nat),
  S n = S m ->
  n = m.

Proof.
  intros n m H.
  inversion H. (* this amounts to adding H1: n = m, replacing n by m *)
  reflexivity. 
  Qed.

Theorem inversion_ex_1: forall (n m o : nat),
  [n;m] = [o;o] ->
  [n] = [m].

Proof.
  intros n m o H.
  inversion H.
  reflexivity.
  Qed.

(* Exercise *)
Example inversion_ex_3:
  forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.

Proof.
  intros X x y z w l j eq1 eq2.
  inversion eq2. inversion eq1. reflexivity.
  Qed.

(* Principle of explosion *)
Theorem inversion_ex_4: forall (n : nat),
  S n = 0 ->
  2 + 2 = 5.

Proof.
  intros n contra.
  inversion contra.
  Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

(* Exercise *)
Example inversion_ex_6: 
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.

Proof.
  intros X x y z l j eq1.
  inversion eq1.
  Qed.

(* Tactics on hypotheses *)

(* `simpl in H` performs simplication in the hypothesis H *)
Theorem S_inj: forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.

Proof.
  intros n m b H.
  simpl in H.
  apply H.
  Qed.

(* Similarly, `apply L in H` matches some conditional statement L against H *)
(* This gives us a form of "forward reasoning" *)
(* In contrast, `apply L` is backward reasoning *)


(* Demonstrating forward reasoning *)
Theorem silly3': forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.

Proof.
  intros n eq H.
  symmetry in H. 
  apply eq in H. (* matches q in p -> q, matching against p *)
  symmetry in H.
  apply H.
  Qed.

(* Exercise *)
Check plus_n_Sm.
(* plus_n_Sm : forall n m : nat, S (n + m) = n + S m *)

Lemma eq_imp_succ: forall n m,
  n = m -> S n = S m.
  intros n m eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem plus_n_n_injective: forall n m,
  n + n = m + m ->
  n = m.

Proof.
  intros n.
  induction n as [| n' ].
  destruct m.
  intro H. reflexivity.
  simpl. intro contra. inversion contra.
  destruct m as [| m' ].
  intro H.
  - simpl in H. inversion H.
  - intro H.
    apply eq_imp_succ.
    apply IHn'.
    simpl in H.
    inversion H.
    rewrite <- plus_n_Sm in H1.
    rewrite <- plus_n_Sm in H1.
    inversion H1.
    reflexivity.
  Qed.

(* Exercise *)
Theorem beq_nat_true:
  forall n m,
  beq_nat n m = true ->
  n = m.

Proof.
  intros n.
  induction n as [| n' IHn' ].
  - simpl. destruct m.
    + intro H. reflexivity.
    + intro contra. inversion contra.
  - intro m. destruct m as [| m' ].
    + simpl. intro contra. inversion contra.
    + simpl. intro H. 
      apply eq_imp_succ. 
      apply IHn'. inversion H.
      reflexivity.
  Qed.

(* Demonstrating `generalize independent` *)
(* Pattern: introduce all quantified variables, *)
(* then re-generalize one or more of them, *)
(* selectively taking variables out of the context *)
(* and putting them back at the beginning of the goal *)
Theorem double_injective: 
  forall n m,
  double n = double m ->
  n = m.

Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* n is back in goal, and we can do induction on m *)
  (* and get a sufficiently general IH *)
  induction m as [| m' ].
  - simpl. intros n eq. destruct n as [| n' ].
    + reflexivity.
    + inversion eq.
  - simpl. intros n eq. destruct n as [| n' ].
    + inversion eq.
    + apply f_equal.  apply IHm'. inversion eq. reflexivity.
  Qed.

(* needed in later chapters *)
Theorem beq_id_true:
  forall x  y,
  NatList.beq_id x y = true ->
  x = y.

Proof.
  intros [m] [n].
  simpl. intros H.
  assert (H' : m = n).
    - apply beq_nat_true. apply H.
    - rewrite H'. reflexivity.
  Qed.

(* Exercise *)
Check nth_error.

Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.

Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| l' ].
  - simpl. intros n eq. destruct n as [| n' ].
    + simpl. reflexivity.
    + inversion eq.
  - simpl. intros n eq. destruct n as [| n' ].
    + simpl. inversion eq. 
    + simpl. rewrite IHl.
      * reflexivity.
      * inversion eq. reflexivity.
  Qed.

(* Demonstrating unfolding of definitions *)
Definition square n := n * n.

Lemma square_mult:
  forall n m,
  square (n * m) = square n * square m.

Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  - rewrite mult_comm. apply mult_assoc.
  - rewrite H.  rewrite mult_assoc. reflexivity.
  Qed.