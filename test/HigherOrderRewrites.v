Require Import ZArith.
Require Import Classical.

Require Import CalTac.Core.

Lemma not_exists_iff_forall_not:
  forall T (P : T -> Prop),
    ~ex P <-> (forall x, ~P x).
Proof.
  obvious.
Qed.

#[local] Hint Rewrite not_exists_iff_forall_not : normalize.

Lemma not_all_iff_ex_not:
  forall T (P : T -> Prop),
    ~(forall x, P x) <-> (exists x, ~P x).
Proof.
  obvious using not_all_ex_not.
Qed.

#[local] Hint Rewrite not_all_iff_ex_not : normalize.

Lemma not_true_iff_false:
  ~True <-> False.
Proof.
  obvious.
Qed.

#[local] Hint Rewrite not_true_iff_false : normalize.

Lemma not_false_iff_true:
  ~False <-> True.
Proof.
  obvious.
Qed.

#[local] Hint Rewrite not_false_iff_true : normalize.

Lemma test:
  forall T,
    ~(exists (x : T), forall (y : T), ~forall (z : T), True).
Proof.
  Fail lazy_match! goal with [ |- exists _, (forall _, True) ] => () end.
  nf.
  lazy_match! goal with [ |- exists _, (forall _, True) ] => () end.
  obvious.
Qed.
