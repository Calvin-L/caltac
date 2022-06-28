Require Export Coq.Logic.Classical.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.Classical_Pred_Type.
Require Export CalTac.CalTac.

Lemma not_not:
  forall P, (~~P) <-> P.
Proof.
  obvious using NNPP.
Qed.
#[export] Hint Rewrite not_not : normalize.

Lemma not_and:
  forall P Q, ~(P /\ Q) <-> (~P \/ ~Q).
Proof.
  obvious using not_and_or, or_not_and.
Qed.
#[export] Hint Rewrite not_and : normalize.

Lemma not_forall:
  forall T (P : T -> Prop), (~forall x, P x) <-> (exists x, ~P x).
Proof.
  obvious using not_all_ex_not, ex_not_not_all.
Qed.
#[export] Hint Rewrite not_forall : normalize.
