(*
 * Coq has an incredibly powerful rewrite system, but that power seems to come
 * with a lot of sharp edges.  This library includes a lot of arcane and
 * poorly-documented (or undocumented!) wizardry, and I want to put together a
 * coherent set of justifications for why I made those specific choices.
 *
 * This file was written using Coq 8.16.1, and it is likely to break in future
 * versions as some of these subtle behaviors are subject to change.  It is
 * best experienced interactively.
 *
 * This file builds up to a powerful `rewrite_strat` invocation and set of
 * options that powers the `nf` tactic.
 *)

Require Import Setoid.

Require Import List.
Import ListNotations.

(* ========================================================================= *)

Module FindingObviousRewrites.

  (*
   * Here's the setup: we have a record type that has one field (a set of
   * numbers).
   *)
  Require Import Ensembles.
  Record Foo := { foo_prop: Ensemble nat }.

  (*
   * We want to define a straightforward rewrite rule that simplifies
   * projecting the field out of a record.
   *
   * A quick aside here: Coq pros might wonder why you would want this at all.
   * A simple `cbn [foo_prop]` will do this rewrite faster in all cases.  I
   * would urge those people not to get too bogged down in the specifics of our
   * definitions; you could imagine `foo_prop` is just "some function" and the
   * record construction is just "another function" and the fact that my
   * definitions are amenable to `cbn` is just because I'm trying to keep
   * things simple.
   *)
  Lemma simplify_foo_prop:
    forall p,
      foo_prop {| foo_prop := p |} = p.
  Proof.
    intros; reflexivity.
  Qed.

  (*
   * We obviously want to apply this rewrite a lot, so let's add it to a hint
   * database.
   *)
  #[local] Hint Rewrite simplify_foo_prop : normalize.

  (*
   * Now let's try to do some simple proofs.
   *)
  Lemma foo001:
    (forall x, foo_prop {| foo_prop := fun x => x > 0 |} x) ->
    False.
  Proof.
    (* Rewriting with the hint database fails. *)
    Fail rewrite_strat (hints normalize).

    (* The problem is that `rewrite_strat` does not recurse into subterms by
     * default.  So let's do that using the `bottomup` strategy.  But it
     * doesn't work! *)
    Fail rewrite_strat (bottomup (hints normalize)).

    (* I don't fully understand why that fails.  It may be related to
     * https://github.com/coq/coq/issues/11347 since we are asking for a
     * rewrite that modifies `f` in a term like `f x`.  If you mess around
     * enough you will eventually discover that `old_hints` is a little better
     * at finding the kind of rewrite we're looking for.  However, this new
     * command fails with a truly exotic message:
     *  > Anomaly "Uncaught exception Invalid_argument("decomp_pointwise")."
     * Well heck.
     *
     * Related Coq issues:
     *  https://github.com/coq/coq/issues/4617
     *  https://github.com/coq/coq/issues/8204
     *  https://github.com/coq/coq/issues/11347
     *)
    Fail rewrite_strat (bottomup (old_hints normalize)).

    (* Fortunately this is fixable using the `innermost` or `outermost`
     * strategies.  I have no idea why.  See also this comment:
     * https://github.com/coq/coq/issues/12510#issuecomment-644217566
     *)
    rewrite_strat (innermost (old_hints normalize)).

    (* The goal is now what we expect. *)
    match goal with [ |- (forall _, _ > 0) -> False ] => idtac end.
  Abort.

  (* Unfortunately our new rewrite strategy doesn't quite work... *)
  Lemma nil_eq_app_iff:
    forall T (l1 l2 : list T),
      [] = l1 ++ l2 <-> (l1 = [] /\ l2 = []).
  Proof.
    destruct l1; cbn [List.app] in *; intuition (discriminate || auto).
  Qed.

  #[local] Hint Rewrite nil_eq_app_iff : normalize.


  (* A quick demo *)
  Lemma find_first_spec_nil:
    forall T (prefix : list T) x suffix,
      [] = prefix ++ [x] ++ suffix ->
      False.
  Proof.
    rewrite_strat (innermost (old_hints normalize)).
  Abort.

  (* Another demo. *)
  Lemma foo002:
    foo_prop {| foo_prop := fun x => x > 0 |} = (fun x => x > 0).
  Proof.
    rewrite_strat (innermost (old_hints normalize)).
    match goal with [ |- ?x = ?x ] => idtac end.
  Abort.

End FindingObviousRewrites.

(* ========================================================================= *)

Module DefinitionalEquivalenceAndOpaquenessAndUnfolding.

  (*
   * Here's an obvious rewrite rule we might want:
   *)
  Lemma in_nil_iff:
    forall T (x : T),
      List.In x nil <-> False.
  Proof.
    unfold List.In.
    tauto.
  Qed.
  #[local] Hint Rewrite in_nil_iff : normalize.

  (*
   * Coq pros might immediately recognize our "mistake", but I think it's
   * highly nonobvious and shouldn't be a mistake at all.
   *
   * We have essentially written the following rewrite rule:
   *
   *    False <-> False
   *
   * When we use this rule with `rewrite_strat`, Coq will unfold definitions,
   * apply our rewrite rule, and then think it has made progress because the
   * new goal is syntactically different from the old one.  That might be OK,
   * except that `in_nil_iff` requires arguments `T` and `x`!  We will get some
   * spurious and confusing subgoals to provide those whenever Coq decides to
   * apply our rewrite.
   *
   * Let's see that in action with some proofs about `find_first_spec`.
   *)
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
    intros.

    (* This works!?  Yes, because our goal is definitionally equal to False
     * and because the left side of `in_nil_iff` is ALSO definitionally equal
     * to False. *)
    setoid_rewrite in_nil_iff.
    Undo.

    (*
     * The Coq Manual suggests using `Hint Opaque NAME : typeclass_instances`
     * to control unfolding.  This doesn't appear to do anything.
     *)
    #[local] Hint Opaque List.In : typeclass_instances.
    #[local] Hint Opaque find_first_spec : typeclass_instances.
    #[local] Hint Opaque iff : typeclass_instances.
    #[local] Hint Opaque in_nil_iff : typeclass_instances.
    setoid_rewrite in_nil_iff. (* still manages to apply in_nil_iff *)
    Undo.

    (* Autorewrite also finds it. *)
    autorewrite with normalize.
    Undo.

    (* Amazingly, rewrite_strat fails to find the same rewrite.  I have no idea
     * why! *)
    Fail rewrite_strat (innermost (old_hints normalize)).

    (* We can control unfolding using the (undocumented?) `rewrite` hint
     * database. *)
    #[local] Hint Opaque List.In : rewrite.
    Fail setoid_rewrite in_nil_iff.
    Undo.
    Undo.

    (* But it's a pain in the butt to remember to do that with every
     * definition, including the ones in the standard library.  Therefore,
     * we opt for the much simpler: *)
    #[local] Hint Constants Opaque : rewrite.
    Fail setoid_rewrite in_nil_iff.
  Abort.

End DefinitionalEquivalenceAndOpaquenessAndUnfolding.

(* ========================================================================= *)

(*
 * I am still considering if this is a good idea:
 *
 * #[export] Hint Constants Opaque : rewrite.
 *
 * But this one for sure:
 *
 * rewrite_strat (innermost (old_hints normalize))
 *
 * See also:
 * https://coq.inria.fr/refman/addendum/generalized-rewriting.html
 * https://coq.inria.fr/refman/addendum/type-classes.html#coq:cmd.Typeclasses-Opaque
 * https://coq.inria.fr/refman/proofs/automatic-tactics/auto.html#hint-databases-defined-in-the-coq-standard-library
 * https://github.com/coq/coq/issues/12510
 * https://github.com/coq/coq/issues/12053
 * https://github.com/coq/coq/issues/13576
 * https://github.com/coq/coq/issues/14132
 * https://github.com/coq/coq/issues/1811
 * https://github.com/coq/coq/issues/4617
 * https://github.com/coq/coq/issues/8204
 * https://github.com/coq/coq/issues/11347
 *)
