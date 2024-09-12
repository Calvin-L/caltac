Require Import CalTac.Core.

Lemma not_true:
  ~True <-> False.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite not_true : nf.

Lemma not_false:
  ~False <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite not_false : nf.

Lemma or_true_P:
  forall P, (True \/ P) <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite or_true_P : nf.

Lemma or_false_P:
  forall P, (False \/ P) <-> P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite or_false_P : nf.

Lemma or_P_true:
  forall P, (P \/ True) <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite or_P_true : nf.

Lemma or_P_false:
  forall P, (P \/ False) <-> P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite or_P_false : nf.

Lemma and_true_P:
  forall P, (True /\ P) <-> P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite and_true_P : nf.

Lemma and_false_P:
  forall P, (False /\ P) <-> False.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite and_false_P : nf.

Lemma and_P_true:
  forall P, (P /\ True) <-> P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite and_P_true : nf.

Lemma and_P_false:
  forall P, (P /\ False) <-> False.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite and_P_false : nf.

Lemma implies_true_P:
  forall P : Prop, (True -> P) <-> P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite implies_true_P : nf.

Lemma implies_false_P:
  forall P : Prop, (False -> P) <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite implies_false_P : nf.

Lemma implies_P_true:
  forall P : Prop, (P -> True) <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite implies_P_true : nf.

Lemma implies_P_false:
  forall P : Prop, (P -> False) <-> ~P.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite implies_P_false : nf.

Lemma not_or:
  forall P Q, ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
  obvious.
Qed.
#[export] Hint Rewrite not_or : nf.

Lemma not_exists:
  forall T (P : T -> Prop), (~ex P) <-> (forall x, ~P x).
Proof.
  obvious.
Qed.
#[export] Hint Rewrite not_exists : nf.

Lemma forall_true:
  forall T,
    (forall x : T, True) <-> True.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite forall_true : nf.

Lemma exists_false:
  forall T,
    ex (fun x : T => False) <-> False.
Proof.
  obvious.
Qed.
#[export] Hint Rewrite exists_false : nf.
