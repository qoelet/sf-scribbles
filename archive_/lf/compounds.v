Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
    | black => true
    | white => true
    | primary p => false
  end.

Definition isblue (c : color) : bool :=
  match c with
    | primary blue => true
    | _ => false
  end.

Example test_isblue_1: (isblue (primary blue)) = true.
Proof. simpl. reflexivity. Qed.
Example test_isblue_2: (isblue (primary green)) = false.
Proof. simpl. reflexivity. Qed.
Example test_isblue_3: (isblue black) = false.
Proof. simpl. reflexivity. Qed.
