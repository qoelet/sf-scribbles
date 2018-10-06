Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition not (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition and (b₁ : bool) (b₂ : bool) : bool :=
  match b₁ with
   | true => b₂
   | false => false
  end.

Definition or (b₁ : bool) (b₂ : bool) : bool :=
  match b₁ with
   | true => true
   | false => b₂
  end.

(* Unit tests *)
Example test_or_1: (or true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_or_2: (or false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_or_3: (or false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_or_4: (or true true) = true.
Proof. simpl. reflexivity. Qed.

(* Introduce notations *)
Notation "x && y" := (and x y).
Notation "x || y" := (or x y).

Example test_or_5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise: implement nand *)
Definition nand (b₁ : bool) (b₂ : bool) : bool :=
  match b₁ with
    | true => not b₂
    | false => true
  end.

Example test_nand_1: (nand true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_2: (nand false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_3: (nand false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_4: (nand true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: implement and3 *)
Definition and3 (b₁ : bool) (b₂ : bool) (b₃ : bool) : bool :=
  match b₁ with
    | true =>
      match b₂ with
        | true => b₃
        | false => false
      end
    | false => false
  end.

Example test_and3_1: (and3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_and3_2: (and3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and3_3: (and3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and3_4: (and3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* We can check the type of an expression *)
Check not.
