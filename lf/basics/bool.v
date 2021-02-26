Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* Complete specification for orb; a truth table *)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

(* Complete specification for andb *)
Example test_andb1: (andb true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (andb false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb3: (andb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb4: (andb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Introducing infix notation via [Notation] *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
Example test_andb5: true && true && false = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: nandb *)
Definition nandb (b1 : bool) (b2: bool) : bool :=
  (negb (andb b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: andb3 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
