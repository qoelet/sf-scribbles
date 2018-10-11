(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
Add LoadPath "lf/"
Require Import lists.

(* Polymorphic lists *)
Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count')
  end.

Example test_repeat_1:
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Proof.
  reflexivity. Qed.

Example test_repeat_2:
  repeat bool false 1 = cons bool false (nil bool).

Proof.
  reflexivity. Qed.

(* Exercise *)
Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.

(* Demonstrating type inference *)
Fixpoint repeat' X x count : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat' X x count')
  end.

(* and holes *)
Fixpoint repeat'' X x count : list X :=
  match count with
    | 0 => nil _
    | S count' => cons _ x (repeat'' _ x count')
  end.

(* and `Arguments` directive *)
Arguments nil {X}.
Arguments cons {X}.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
    | 0 => nil
    | S count' => cons x (repeat''' x count')
  end.

Check repeat.
Check repeat'.
Check repeat''.
Check repeat'''.

(* Reimplementing some standard list functions on the new polymorphic lists *)
Fixpoint app {X : Type} (m n : list X) : list X :=
  match m with
    | nil => n
    | cons h t => cons h (app t n)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
    | nil => nil
    | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    | nil => 0
    | cons _ l' => S (length l')
  end.

Example test_rev_1:
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).

Proof.
  reflexivity. Qed.

Example test_rev_2:
  rev (cons true nil) = cons true nil.

Proof.
  reflexivity. Qed.

Example test_length_1:
  length (cons 1 (cons 2 (cons 3 nil))) = 3.

Proof.
  reflexivity. Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Exercise *)
Theorem app_nil_r: forall (X : Type), forall l : list X,
  l ++ [] = l.

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
  Qed.

Theorem app_assoc: forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
  Qed.

Lemma app_length: forall (X : Type) (m n : list X),
  length (m ++ n) = length m + length n.

Proof.
  intros.
  induction m as [| l m' IHm' ].
  - simpl. reflexivity.
  - simpl. rewrite -> IHm'. reflexivity.
  Qed.

(* Exercise *)
Theorem rev_app_distr: forall X (m n : list X),
  rev (m ++ n) = rev n ++ rev m.

Proof.
  intros.
  induction m as [| k m' IHm' ].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHm', app_assoc. reflexivity.
  Qed.

(* Exercise *)
Theorem rev_involutive: forall X : Type, forall l : list X,
  rev (rev l) = l.

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    simpl. rewrite IHl'.
    reflexivity.
  Qed.

(* Demonstrating polymorphic pairs *)
Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
    | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X * Y) :=
  match lx, ly with
    | [], _ => []
    | _, [] => []
    | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Exercise *)
Compute (combine [1;2] [false;false;true;true]).

(* Exercise *)
Fixpoint iter_fst {X Y : Type} (l : list (X * Y))
  : list X :=
  match l with
    | [] => nil
    | p :: t => cons (fst p) (iter_fst t)
  end.

Fixpoint iter_snd {X Y : Type} (l : list (X * Y))
  : list Y :=
  match l with
    | [] => nil
    | p :: t => cons (snd p) (iter_snd t)
  end.

Definition split {X Y : Type} (l : list (X * Y))
  : (list X) * (list Y) := (iter_fst l, iter_snd l).

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).

Proof.
  reflexivity. Qed.

(* Introducing functions *)
Definition doit3times {X : Type} (f: X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)
Example test_doit3times: doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
  : (list X) :=
  match l with
    | [] => []
    | h :: t =>
      if test h
        then h :: (filter test t)
        else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.
Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Demonstrating anonymous functions *)
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.

Proof.
  reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1)
    [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].

Proof. reflexivity. Qed.

(* Exercise *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => bgt_nat x 7) (filter even l).

Compute filter_even_gt7  [1;2;6;9;10;3;12;8].

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].

Proof.
  reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].

Proof.
  reflexivity. Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).

Proof.
  reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).

Proof.
  reflexivity. Qed.

(* Map *)
Fixpoint map {X Y : Type} (f: X -> Y) (l: list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercise *)
Lemma map_app_distr:
  forall (X Y : Type) (f: X -> Y) (l: list X) (m: list X),
  map f (l ++ m) = (map f l) ++ (map f m).

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
  Qed.

Theorem map_rev :
  forall (X Y : Type) (f: X -> Y) (l: list X),
  map f (rev l) = rev (map f l).

Proof.
  intros.
  induction l as [| k l' IHl' ].
  - simpl. reflexivity.
  - simpl.
    rewrite -> map_app_distr.
    simpl.
    rewrite -> IHl'.
    reflexivity.
  Qed.

(* Exercise *)
Fixpoint flat_map
  {X Y: Type} (f: X -> list Y) (l: list X)
  : (list Y) :=
  match l with
    | nil => nil
    | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].

Proof.
  reflexivity. Qed.

(* Demonstrating fold *)
Fixpoint fold {X Y : Type} (f: X -> Y -> Y)
  (l: list X) (b: Y) : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof.
  reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof.
  reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof.
  reflexivity. Qed.

End MumbleGrumble.
