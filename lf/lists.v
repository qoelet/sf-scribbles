Add LoadPath "lf/".
Require Import numbers.
Require Import induction.

Module NatList.

(* Pairs of numbers *)
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

(* List of numbers *)
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* Example: a three-element list *)
Definition fooList := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" :=
  (cons x l)
  (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Some functions for working with lists *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (m n : natlist) : natlist :=
  match m with
    | nil => n
    | h :: t => h :: (app t n)
  end.

Notation "x ++ y" :=
  (app x y)
  (right associativity, at level 60).

Example test_app: [1;2;3] ++ [4;5;6] = [1;2;3;4;5;6].
Proof.
  reflexivity.
  Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

(* Exercise *)
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t =>
      match h with
        | 0 => nonzeros t
        | s => s :: (nonzeros t)
      end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].

Proof.
  reflexivity.
  Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t =>
      match (odd h) with
        | true => h :: (oddmembers t)
        | false => oddmembers t
      end
    end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].

Proof.
  reflexivity.
  Qed.

Definition countoddmembers (l : natlist) : nat
  := length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.

Proof.
  reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.

Proof.
  reflexivity. Qed.

 Example test_countoddmembers3:
  countoddmembers nil = 0.

Proof.
  reflexivity. Qed.

(* Exercise *)
Fixpoint alternate (m n : natlist) : natlist :=
  match m with
    | nil => n
    | h :: t =>
      match n with
        | nil => h :: t
        | x :: y => h :: x :: (alternate t y)
      end
    end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].

Proof.
  reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].

Proof.
  reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].

Proof.
  reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].

Proof.
  reflexivity. Qed.

Definition bag := natlist.

(* Exercise *)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => 0
    | h :: t =>
      match (beq_nat v h) with
        | true => 1 + count v t
        | false => count v t
      end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.

Proof.
  reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.

Proof.
  reflexivity. Qed.

(* Exercise *)
Definition sum : bag -> bag -> bag := alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.

Proof.
  reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  match s with
    | nil => v :: nil
    | h :: t => v :: h :: t
  end.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.

Proof.
  reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.

Proof.
  reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  match (count v s) with
    | 0 => false
    | _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.

Proof.
  reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.

Proof.
  reflexivity. Qed.

(* Demonstrating induction on lists *)
Theorem app_assoc : forall l m n : natlist,
  (l ++ m) ++ n = l ++ (m ++ n).

Proof.
  intros.
  induction l as [| k l' IHl1' ].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
  Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(* Lemma for proving the next theorem *)
Theorem app_length: forall m n : natlist,
  length (m ++ n) = (length m) + (length n).

Proof.
  intros m n.
  induction m as [| k m IHm1' ].
  - reflexivity.
  - simpl. rewrite <- IHm1'. reflexivity.
  Qed.

Theorem rev_length: forall l : natlist,
  length (rev l) = length l.

Proof.
  intros l.
  induction l as [| n l' IHl' ].
  - reflexivity.
  - simpl.
    rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'.
    reflexivity.
  Qed.

(* Exercise *)
Theorem app_nil_r: forall l : natlist,
  l ++ [] = l.

Proof.
  intros l.
  induction l as [| n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
  Qed.

(* Exercise *)
Lemma rev_nil_r: forall l : natlist,
  rev l ++ [] = rev l.

Proof.
  intros l.
  induction l as [| n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl', app_assoc. simpl. reflexivity.
  Qed.

Theorem rev_app_distr: forall m n : natlist,
  rev (m ++ n) = rev n ++ rev m.

Proof.
  intros m n.
  induction m as [| k m' IHm' ].
  - simpl. rewrite -> rev_nil_r. reflexivity.
  - simpl. rewrite -> IHm', app_assoc. reflexivity.
  Qed.

(* Exercise *)
Lemma foo: forall (l : natlist) (v : nat),
  rev l ++ [v] = rev (v :: l).

Proof.
  intros l v.
  induction l as [| n l' IHl' ].
  - simpl. reflexivity.
  - simpl. reflexivity.
  Qed.

Theorem rev_involutive: forall l : natlist,
  rev (rev l) = l.

Proof.
  intros l.
  induction l as [| n l' IHl' ].
  - simpl. reflexivity.
  - simpl.
    rewrite -> foo.
    simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IHl'.
    reflexivity.
  Qed.

(* Exercise *)
Theorem app_assoc4: forall l m n o : natlist,
  l ++ (m ++ (n ++ o)) = ((l ++ m) ++ n) ++ o.

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. rewrite <- app_assoc. reflexivity.
  - simpl.
    rewrite -> app_assoc.
    rewrite -> app_assoc.
    reflexivity.
  Qed.

(* Exercise *) (* This was crazy! *)
Lemma nonzeros_app: forall m n : natlist,
  nonzeros (m ++ n) = (nonzeros m) ++ (nonzeros n).

Proof.
  intros m n.
  induction m as [| k m' IHm' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHm'. induction n as [| l n' IHn' ].
    + simpl.
      rewrite -> app_nil_r.
      rewrite -> app_nil_r.
      reflexivity.
    + simpl. destruct k.
      * reflexivity.
      * simpl. reflexivity.
  Qed.

End NatList.
