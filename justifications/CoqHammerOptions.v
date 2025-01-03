Require Import Ltac2.Ltac2.
Require Import Arith.
Require Import String.
Require Import List.

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


(*
 * Undirected rewrites seem to create problems.  `hauto` with `urew` option on
 * (default) will spin out here.
 *)
Inductive Partial T := Exact : T -> Partial T | Unknown : string -> Partial T.
Arguments Exact [_].
Arguments Unknown [_].
Lemma no_undirected_rewrites:
  forall T (f : T -> T -> Partial bool) a b c,
    (forall x y z : T, f x y = Exact true -> f y z = Exact true -> f x z = Exact true) ->
    (forall x : T, In x a -> exists witness : T, In witness b /\ f x witness = Exact true) ->
    (forall x : T, In x b -> exists witness : T, In witness a /\ f x witness = Exact true) ->
    (forall x : T, In x b -> exists witness : T, In witness c /\ f x witness = Exact true) ->
    (forall x : T, In x c -> exists witness : T, In witness b /\ f x witness = Exact true) ->
    (forall x : T, In x a -> exists witness : T, In witness c /\ f x witness = Exact true) /\
    (forall x : T, In x c -> exists witness : T, In witness a /\ f x witness = Exact true).
Proof.
  ltac1:(hauto urew:off).
Qed.
