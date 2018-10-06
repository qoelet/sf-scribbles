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
