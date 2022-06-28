Require Import Ltac2.Ltac2.
Require Import Arith.

From Hammer Require Import Tactics.

(*
 * sauto can miss obvious solutions---here it just needs to instantiate
 * a hypothesis, but gets distracted somehow (presumably destructing x or
 * the proof of x/10 < x or something).
 *
 * So: `hauto` is a better choice.
 *)
Lemma wtf:
  forall x,
    1 < 10 ->
    0 < x ->
    (forall a b : nat,
      0 < a ->
      1 < b ->
      a / b < a) ->
    x / 10 < x.
Proof.
  Fail ltac1:(sauto).
  ltac1:(hauto).
Qed.
