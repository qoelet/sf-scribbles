(* Define a new type *)
Inductive day : Type :=
  | mon : day
  | tue : day
  | wed : day
  | thu : day
  | fri : day
  | sat : day
  | sun : day.

(* Write a function to operate on above type *)
Definition next_day (d : day) : day :=
  match d with
    | mon => tue
    | tue => wed
    | wed => thu
    | thu => fri
    | fri => sat
    | sat => sun
    | sun => mon
  end.

(* Compute some examples *)
Compute (next_day fri).
Compute (next_day (next_day mon)).

(* Make an assertion *)
Example test_next_day:
  (next_day (next_day fri)) = sun.

(* Ask Coq to verify assertion *)
Proof. simpl. reflexivity. Qed.
