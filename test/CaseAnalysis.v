Require Import CalTac.CalTac.

Inductive Enum : Set :=
  A | B | C.

Lemma test:
  forall x y,
    (x > 0) \/ (x < 0) ->
    match y with
    | A => (x = 1 <-> x = 2)
    | B => True
    | C => False
    end.
Proof.
  case_analysis; try (obvious).
Abort.
