Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/".
Require Import numbers.
Require Import induction.
Require Import poly.
Require Import tactics.
Require Import Coq.Lists.List.
Open Scope list_scope.

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

(* Conjuction *)
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

(* Demonstrating `destruct` for using a conjunctive hypothesis to help prove stuff *)
Lemma and_example_2:
  forall n m : nat,
  n = 0 /\ m = 0 ->
  n + m = 0.

Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
  Qed.

Lemma and_example_3:
  forall n m : nat,
  n + m = 0 ->
  n * m = 0.

Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  - apply and_exercise. apply H.
  - destruct H' as [Hn Hm].
    + rewrite Hn. reflexivity.
  Qed.

Lemma proj1:
  forall P Q : Prop,
  P /\ Q -> P.

Proof.
  intros P Q [HP HQ].
  apply HP.
  Qed.

(* Exercise *)
Lemma proj2:
  forall P Q : Prop,
  P /\ Q -> Q.

Proof.
  intros P Q [HP HQ].
  apply HQ.
  Qed.

Theorem and_commut:
  forall P Q : Prop,
  P /\ Q -> Q /\ P.

Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
  Qed.

(* Exercise *)
Theorem and_assoc:
  forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.

Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
  Qed.

(* Disjunction *)
Lemma or_example:
  forall n m : nat,
  n = 0 \/ m = 0 ->
  n * m = 0.

Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. 
    rewrite <- mult_n_O.
    reflexivity.
  Qed.

Lemma or_intro: 
  forall A B : Prop,
  A -> A \/ B.

Proof.
  intros A B HA.
  left.
  apply HA.
  Qed.

Lemma zero_or_succ:
  forall n : nat,
  n = 0 \/ n = S (pred n).

Proof.
  intros [| n ].
  - left. reflexivity.
  - right. reflexivity.
  Qed.

(* Demonstrating negation, falsehood *)
Module MyNot.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet:
  forall (P : Prop),
  False -> P.

Proof.
  intros P contra.
  destruct contra.
  Qed.

(* Exercise *)
Fact not_implies_our_not:
  forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).

Proof.
  intros.
  destruct H.
  apply H0.
  Qed.

Theorem zero_not_one: ~ (0 = 1).

Proof.
  intros contra.
  inversion contra.
  Qed.

(* Inequality notation *)
Check (0 <> 1).

Theorem zero_not_one': 0 <> 1.

Proof.
  intros H.
  inversion H.
  Qed.

Theorem not_False:
  ~ False.

Proof.
  unfold not.
  intros H.
  apply H.
  Qed.

Theorem contradiction_implies_anything:
  forall P Q : Prop,
  (P /\ ~ P) -> Q.

Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
  Qed.

Theorem double_neg:
  forall P : Prop,
  P -> ~~P.

Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
  Qed.

(* Exercise *)
Theorem contrapositive:
  forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).

Proof.
  intros P Q HP HNQ HNP.
  unfold not in HNQ.
  apply HNQ in HP.
  - apply HP.
  - apply HNP.
  Qed.

(* Exercise *)
Theorem not_both_true_and_false:
  forall P : Prop,
  ~ (P /\ ~P).

Proof.
  intros P contra.
  destruct contra as [H HN].
  unfold not in HN.
  apply HN in H.
  apply H.
  Qed.

Theorem not_true_is_false:
  forall b : bool,
  b <> true -> b = false.

Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
  Qed.

(* Coq has a built-in tactic `exfalso` for applying reasoning with `ex_falso_quodlibet` *)
Theorem not_true_is_false':
  forall b : bool,
  b <> true -> b = false.

Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
  Qed.

(* Truth *)
(* `I` is a predefined constant `I : True` *)
Lemma True_is_true : True.

Proof.
  apply I. Qed.

(* Logical equivalence *)
Module MyIff.

Definition iff (P Q : Prop) := 
  (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym:
  forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).

Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
  Qed.

Lemma not_true_iff_false:
  forall b, b <> true <-> b = false.

Proof.
  intros b.
  split.
  - unfold not. apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'.
  Qed.

(* Exercise *)
Theorem or_distributes_over_and:
  forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).

Proof.
  Admitted.

(* Existential quantification *)
Lemma four_is_even:
  exists n : nat,
  4 = n + n.

Proof.
  exists 2. reflexivity.
  Qed.

Theorem exists_example_2:
  forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).

Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
  Qed.

(* Exercise *)
Theorem dist_not_exists:
  forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).

Proof.
  intros.
  unfold not. intros H2. destruct H2 as [x E].
  apply E. apply H.
  Qed.

Fixpoint In
  {A : Type} (x : A) (l : list A) : Prop :=
  match l with
    | nil => False
    | x' :: l' => x' = x \/ In x l'
  end.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" :=
  (cons x .. (cons y nil) ..).

Example In_example_1:
  In 4 [ 1; 2; 3; 4; 5 ].

Proof.
  simpl. right. right. right. left. reflexivity.
  Qed.

