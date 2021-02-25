(* Example of an enumerated type *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Example of a function that operates on day *)
Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

(* Test function works; there are 3 ways *)

(* 1. Use Compute on a compound expression *)
Compute (next_weekday monday).

(* 2. Record what we expect the result to be as a Coq example *)
Example test_next_weekday:
  (next_weekday (next_weekday wednesday)) = friday.
Proof. simpl. reflexivity. Qed.

(* 3. Extract from our Definition, a program in another language *)
