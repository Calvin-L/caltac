Require Import CalTac.CalTac.

Lemma strong_induction:
  forall P : nat -> Prop,
    (forall n, (forall m, m < n -> P m) -> P n) ->
    (forall x, P x).
Proof.

  nf.
  suffices (forall m, m < x -> P m) by obvious.
  induction x; nf.

  - suffices (~(m < 0)) by obvious.
    obvious.

  - assert (m <= x) by obvious.
    cases (m < x \/ m = x).
    + obvious.
    + obvious.

Qed.

Fixpoint fib x :=
  match x with
  | 0 => 1
  | 1 => 1
  | S n => fib n + fib (n-1)
  end.

Lemma fib_positive:
  forall x, fib x > 0.
Proof.
  induction x using strong_induction.
  suffices (match x with
    | 0 => 1
    | 1 => 1
    | S n => fib n + fib (n-1)
    end > 0) by obvious.
  obvious.
Qed.
