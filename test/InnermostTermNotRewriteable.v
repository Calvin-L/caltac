(*
 * A quick example of `rewrite_strat`'s `innermost` and `outermost` tactics,
 * and why `outermost` is probably better...
 *)

Require Import CalTac.CalTac.
Require Import Setoid.

Section innermost.

  Variable State : Type.
  (* Variable U : Set. *)
  (* Variable f : T -> U. *)

  Variable unchanged : forall {T} (f : State -> T) (x y : State), Prop.

  Axiom prove_unchanged:
    forall T (x : State -> T) st st',
      (unchanged x) st st' <-> (x st = x st').
  #[local] Hint Rewrite prove_unchanged : nf.

  Variable P : forall (R : State -> State -> Prop), Prop.

  Axiom prove_P:
    forall R,
      P R <-> forall w w', R w w'.
  #[local] Hint Rewrite prove_P : nf.

  Variable f : State -> nat.

  Lemma test:
    P (fun w w' => unchanged f w w').
  Proof.
    (*
     * Personally, I don't think this should fail, since there *IS* a rewrite
     * in the database that applies.  However, it fails!
     *
     * - prove_unchanged doesn't work because it appears under a function
     *   binder, and there is no morphism that allows rewrite under function
     *   binder.
     * - rewrite_strat seems to get confused and fails because prove_unchanged
     *   does not apply... but shouldn't it try other things in the hintdb,
     *   like prove_P?
     * - maybe I should use outermost instead, to reduce the chance of binders
     *   getting in the way...
     *)
    Fail ltac1:(setoid_rewrite prove_unchanged).
    Fail ltac1:(progress ( rewrite_strat (innermost (hints nf)) )).
    ltac1:(progress ( rewrite_strat (outermost (hints nf)) )).
    ltac1:(progress ( rewrite_strat (outermost (hints nf)) )).
  Abort.

  Lemma test:
    P (fun w w' => unchanged f w w').
  Proof.
    (*
     * Let's make sure `nf` can handle this...
     *)
    nf.
    match! goal with
    | [ |- f _ = f _ ] => ()
    end.
  Abort.

End innermost.
