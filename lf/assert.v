Add LoadPath "lf/".
Require Import induction.

(* Introducing the `assert` tactic *)
Theorem mult_0_plus': forall n m : nat,
  (0 + n) * m = n * m.

Proof.
  intros.
  assert (H: 0 + n = n). (* I choose to use bullets instead *)
  - reflexivity.
  - rewrite -> H.
    reflexivity.
  Qed.

Theorem plus_rearrange: forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).

Proof.
  intros.
  assert (H: n + m = m + n).
  - rewrite -> plus_comm. reflexivity.
  - rewrite -> H. reflexivity.
  Qed.
