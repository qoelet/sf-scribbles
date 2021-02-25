Module Nat.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition succ (n : nat) : nat := S n.

End Nat.

Check (S (S (S O))).

(* Recursion *)
Fixpoint even (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => even n'
  end.

Example test_even_1: even (S (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_even_2: even (S O) = false.
Proof. simpl. reflexivity. Qed.

Definition odd (n : nat) : bool := negb (even n).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(* Exercise: factorial *)
Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => n * factorial n'
  end.

Example test_factorial_1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial_2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x !" := (factorial x)
  (at level 50, left associativity)
  : nat_scope.

Check (5 !).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O =>
      match m with
        | O => true
        | S m' => false
      end
    | S n' =>
      match m with
        | O => false
        | S m' => beq_nat n' m'
      end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => leb n' m'
      end
  end.
Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: blt nat - Tests natural numbers for less than *)
Definition blt_nat (n m : nat) : bool :=
  match beq_nat n m with
    | true => false
    | false => leb n m
  end.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n: forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Mostly equiv in Coq: Theorem, Example, Lemma, Fact, Remark *)

Fact plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example: forall n m : nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into context *)
  intros n m.
  (* move hypothesis into context *)
  intros H.
  (* rewrite goal using hypothesis *)
  rewrite -> H.
  reflexivity.
  Qed.

(* Exercise *)
Theorem plus_id_exercise: forall n m o : nat,
  n = m ->
  m = o ->
  n + m = m + o.

Proof.
  intros n m o.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite <- H2.
  reflexivity. Qed.

(* Rewriting with a previously proven theorem *)
Theorem mult_0_plus: forall n m : nat,
  (0 + n) * m = n * m.

Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.

(* Exercise *)
Theorem mult_S_1: forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.

Proof.
  intros n m.
  intro H.
  rewrite -> H.
  reflexivity. Qed.

(* Case analysis *)
Theorem plus_1_neq_0: forall n : nat,
  beq_nat (n + 1) 0 = false.

Proof.
  intros n.
  destruct n as [| n' ]. (* cases: n = 0, n = S n' *)
  (* bullets for marking proofs to each subgoal *)
  - reflexivity.
  - reflexivity.
  Qed.

Theorem negb_involutive: forall b : bool,
  negb (negb b) = b.

Proof.
  intros b.
  destruct b. (* no `as` clause, no binding required *)
  - reflexivity.
  - reflexivity.
  Qed.

(* Demonstrating nested subgoals *)
Theorem andb_commutative : forall b c, andb b c = andb c b.

Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
  Qed.

(* Demonstrating shorthand for `intros..destruct` *)
Theorem plus_1_neq_0': forall n : nat,
  beq_nat (n + 1) 0 = false.

Proof.
  intros [| n ].
  - reflexivity.
  - reflexivity.
  Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.

Proof.
  intros [] [].
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  Qed.

(* Exercise *)
Theorem andb_true_elim2: forall b c : bool,
  andb b c = true -> c = true.

Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + discriminate.
  - destruct c.
    + reflexivity.
    + discriminate.
  Qed.

(* Exercise *)
Theorem zero_nbeq_plus_1: forall n : nat,
  beq_nat 0 (n + 1) = false.

Proof.
  intros [| n ].
  - reflexivity.
  - reflexivity.
  Qed.

(* Exercise *)
Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

Proof. (* It was more intuitive with the IDE *)
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  Qed.

(* Exercise *)
Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros.
  rewrite H.
  rewrite H.
  rewrite -> negb_involutive.
  reflexivity.
  Qed.

(* Exercise *)
Theorem andb_eq_orb:
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

Proof.
  intros.
  destruct b.
  - destruct c.
    + simpl. reflexivity.
    + simpl. discriminate.
  - destruct c.
    + simpl. discriminate.
    + simpl. reflexivity.
  Qed.

Fixpoint geb (n m : nat) : bool :=
  match n with
    | O => false
    | S n' =>
      match m with
        | O => true
        | S m' => geb n' m'
      end
  end.

Example test_geb2: (geb 4 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_geb3: (geb 2 4) = false.
Proof. simpl. reflexivity. Qed.

Definition bgt_nat (n m : nat) : bool :=
  match beq_nat n m with
    | true => false
    | false => geb n m
  end.

Example test_bgt_nat_1: bgt_nat 2 3 = false.
Proof. 
  reflexivity. Qed.

Example test_bgt_nat_2: bgt_nat 19 3 = true.
Proof. 
  simpl.
  reflexivity. Qed.