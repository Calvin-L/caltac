Require Import CalTac.Core.

Lemma fst_of_pair:
  forall T U (x : T) (y : U),
    fst (x, y) = x.
Proof.
  unfold fst; obvious.
Qed.
#[export] Hint Rewrite fst_of_pair : nf.

Lemma snd_of_pair:
  forall T U (x : T) (y : U),
    snd (x, y) = y.
Proof.
  unfold snd; obvious.
Qed.
#[export] Hint Rewrite snd_of_pair : nf.
