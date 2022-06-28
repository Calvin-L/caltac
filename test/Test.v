Require Import Ensembles.
Require Import String.
Require Import Arith.

Require Import CalTac.CalTac.

Lemma instantiate_iff:
  forall T (x y : Ensemble T),
    (forall a, In _ x a <-> In _ y a) ->
    (forall a, In _ x a -> In _ y a).
Proof.
  nf.
  obvious.
Qed.

Lemma prop_logic:
  forall P Q,
    P \/ Q <-> Q \/ P.
Proof.
  obvious.
Qed.

Lemma find_instantiation:
  forall T (P : T -> Prop) x y (R : T -> T -> Prop) (Q : Prop),
    P x ->
    P y ->
    R x y ->
    (forall a b, P a -> P b -> R a b -> Q) ->
    Q.
Proof.
  obvious.
Qed.

Definition zero := 0.

Lemma definitionally_equal:
  zero = 0.
Proof.
  obvious.
Qed.

Lemma use_after_split:
  forall (P Q : Prop),
    P ->
    Q ->
    P /\ Q.
Proof.
  nf.
  split; obvious using definitionally_equal.
Qed.

Lemma test_suffices:
  forall T (x : T) (P : Prop),
    List.In x nil ->
    P.
Proof.
  nf.
  suffices False. {
    lazy_match! goal with
    | [ h : False |- _ ] => ()
    | [ |- _ ] => fail
    end.
    obvious using definitionally_equal.
  }
  obvious.
Qed.

Lemma exploit_in_nil:
  forall T (x : T) (P : Prop),
    List.In x nil ->
    P.
Proof.
  obvious.
Qed.

Lemma test_suffices2:
  forall T (x : T) (P : Prop),
    List.In x nil ->
    P.
Proof.
  nf.
  suffices False by obvious using definitionally_equal.
  obvious.
Qed.

Lemma test_math:
  forall (P : nat -> Prop),
    (forall y, (forall m, m < y -> P m) -> P y) ->
    P 0.
Proof.
  assert (forall m, ~ (m < 0)) by obvious.
  obvious.
Qed.

Lemma test_math_2:
  forall x y z,
    x < y ->
    y < z ->
    x < z.
Proof.
  obvious.
Qed.

Lemma test_001:
  forall T (a : Ensemble T) (l : list (Ensemble T)) x union_all,
    ((In T (union_all l) x) <-> (exists y, List.In y l /\ In _ y x)) ->
    ((In T a x \/ In T (union_all l) x) <-> (exists y, (y = a \/ List.In y l) /\ In _ y x)).
Proof.
  obvious.
Qed.

Lemma test_002:
  forall T (x y : T) (P : T -> T -> Prop),
    (forall a, P a x <-> P a y) ->
    forall z, P z x <-> P z y.
Proof.
  obvious.
Qed.

Lemma test_003:
  (forall (x : nat) (f g : forall y, y < x -> string),
    (forall y p, f y p = g y p) ->
    (forall a b c d, a = b -> c = d -> a ++ c = b ++ d) ->
    forall pf suffix,
      f (x / 10) pf ++ suffix =
      g (x / 10) pf ++ suffix)%string.
Proof.
  obvious.
Qed.

Lemma test_004:
  forall T (f : T -> T -> T) zero x acc,
    (forall y, f zero y = y) ->
    (forall x y, f x y = f y x) ->
    (forall x y z, f x (f y z) = f (f x y) z) ->
    f acc x = f zero (f x acc).
Proof.
  nf.
  (*
   * NOTE: `ltac1:(simple congruence)` solves this immediately,
   * since it does a few arbitrary instantiations.  I want
   * `obvious` to be at least as powerful.
   *)
  obvious.
Qed.

(*
 * NOTE: this is a very simple goal that requires combining a few different
 * strategies (destruct x; congruence).
 *)
Lemma test_005:
  forall x,
    x <> false ->
    if x then x=true else False.
Proof.
  obvious.
Qed.



(*
 * For reasons nobody understands (as of 2023/2/16), Coq's setoid rewrite
 * machinery fails on certain classes of rewrite rules [1].  This library
 * includes a hacky workaround so these tests can pass.
 *
 * [1]: https://github.com/coq/coq/issues/11347
 *)
Section rewrite_bug_workaround.

Record Foo := { foo_prop: nat -> Prop }.

Lemma simplify_foo_prop:
  forall p,
    foo_prop {| foo_prop := p |} = p.
Proof.
  intros; reflexivity.
Qed.

#[local] Hint Rewrite simplify_foo_prop : normalize.

Lemma test006:
  (forall x, foo_prop {| foo_prop := fun x => x > 0 |} x) ->
  False.
Proof.
  intros.
  Fail lazy_match! goal with [ h : forall _, _ > 0 |- _ ] => () end.
  nf.
  lazy_match! goal with [ h : forall _, _ > 0 |- _ ] => let hh := Control.hyp h in specialize $hh with 0 end.
  obvious.
Qed.

Lemma test007:
  foo_prop {| foo_prop := fun x => x > 0 |} = (fun x => x > 0).
Proof.
  Fail lazy_match! goal with [ |- (fun _ => _) = (fun _ => _) ] => () end.
  nf.
  lazy_match! goal with [ |- (fun _ => _) = (fun _ => _) ] => () end.
  obvious.
Qed.

End rewrite_bug_workaround.


Require Import List.
Import ListNotations.
Section bad_definition_unfolding_workaround.

Lemma in_nil_iff:
  forall T (x : T),
    List.In x nil <-> False.
Proof.
  unfold List.In.
  obvious.
Qed.

#[local] Hint Rewrite in_nil_iff : normalize.

Lemma cons_eq_app_false:
  forall T (x : T) (l : list T),
    (x :: l = []) <-> False.
Proof.
  obvious.
Qed.
#[local] Hint Rewrite cons_eq_app_false : normalize.

Lemma nil_eq_app_iff:
  forall T (l1 l2 : list T),
    [] = l1 ++ l2 <-> (l1 = [] /\ l2 = []).
Proof.
  destruct l1; nf.
  - obvious.
  - suffices (((t :: l1) ++ l2) = (t :: (l1 ++ l2))) by obvious.
    obvious.
Qed.

Lemma app_eq_nil_iff:
  forall T (l1 l2 : list T),
    l1 ++ l2 = [] <-> (l1 = [] /\ l2 = []).
Proof.
  obvious using nil_eq_app_iff.
Qed.

#[local] Hint Rewrite nil_eq_app_iff : normalize.
#[local] Hint Rewrite app_eq_nil_iff : normalize.

Fixpoint find_first_spec {T} (test : T -> Prop) (l : list T) (x : T) : Prop :=
  match l with
  | [] => False
  | (y :: rest) =>
      (test y /\ x = y) \/
      (~test y /\ find_first_spec test rest x)
  end.

Lemma find_first_spec_nil:
  forall T (test : T -> Prop) x prefix suffix,
    [] = prefix ++ [x] ++ suffix ->
    find_first_spec test [] x.
Proof.
  nf.
  lazy_match! goal with [ _ : False |- _ ] => () end.
  obvious.
Qed.

End bad_definition_unfolding_workaround.
