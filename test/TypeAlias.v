Require Import CalTac.Core.

Section type_alias.

Definition T := nat.
Variable P : forall T, T -> T -> Prop.
Axiom P_refl_nat : forall x, P nat x x <-> True.
#[local] Hint Rewrite P_refl_nat : normalize.

(*
 * Rewriting does not "see through" the type alias T to apply P_refl_nat.
 * This is deliberate!  Tactics should not unfold definitions unless told
 * to do so.
 *)
Lemma test001:
  forall x : T,
    P T x x.
Proof.
  nf.
  Fail lazy_match! goal with [ |- True ] => () end.
Abort.

(*
 * With an unfolding hint, T gets unfolded into nat and then P_refl_nat
 * can be applied.
 *)
#[local] Hint Unfold T : normalize.
Lemma test002:
  forall x : T,
    P T x x.
Proof.
  nf.
  exact I.
Qed.

End type_alias.
