Require Import CalTac.Classical.

Lemma test:
  ~forall (x : nat),
    ~~(x = 0).
Proof.
  nf.
  lazy_match! goal with [ |- exists n, n <> 0 ] => () end.
  obvious.
Qed.
