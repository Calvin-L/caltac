Require Import String.
Require Import List.

From CalTac Require Import Internals.
From CalTac Require Import CalTac.
From Hammer Require Import Tactics.

Inductive Partial T := Exact : T -> Partial T | Unknown : string -> Partial T.
Arguments Exact [_].
Arguments Unknown [_].

Goal
  forall T (f : T -> T -> Partial bool) a b c,
    (forall x y z : T, f x y = Exact true -> f y z = Exact true -> f x z = Exact true) ->
    (forall x : T, In x a -> exists witness : T, In witness b /\ f x witness = Exact true) ->
    (forall x : T, In x b -> exists witness : T, In witness a /\ f x witness = Exact true) ->
    (forall x : T, In x b -> exists witness : T, In witness c /\ f x witness = Exact true) ->
    (forall x : T, In x c -> exists witness : T, In witness b /\ f x witness = Exact true) ->
    (forall x : T, In x a -> exists witness : T, In witness c /\ f x witness = Exact true) /\
    (forall x : T, In x c -> exists witness : T, In witness a /\ f x witness = Exact true).
Proof.
  obvious.
Qed.
