Add LoadPath "lf/".
Require Import numbers.
Require Import induction.

Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (snd (4, 7)).

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x, y) => (y, x)
  end.

(* Proving some simple facts about pairs *)
Theorem  surjective_pairing: forall (p : natprod),
  p = (fst p, snd p).

Proof.
  intros p.
  destruct p as [n m].
  (* only one subgoal, since natprods can only be constructed one way *)
  - simpl. reflexivity.
  Qed.

(* Exercise *)
Theorem snd_fst_is_swap: forall (p : natprod),
  (snd p, fst p) = swap_pair p.

Proof.
  intros p.
  destruct p as [n m].
  - simpl. reflexivity.
  Qed.

(* Exercises *)
Theorem fst_swap_is_snd: forall (p : natprod),
  fst (swap_pair p) = snd p.

Proof.
  intros p.
  destruct p as [n m].
  - simpl. reflexivity.
  Qed.

End NatList.
