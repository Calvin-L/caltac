Require Import Setoid.

Record Foo := { foo_field: nat -> Prop }.

Lemma simplify_foo_field:
  forall p,
    foo_field {| foo_field := p |} = p.
Proof.
  intros; reflexivity.
Qed.

#[local] Hint Rewrite simplify_foo_field : normalize.

Lemma segfault:
  True.
Proof.
  (*
   * The cause of this segfault is unclear to me, but it's worth noting that
   * `bottomup` (and its dual `topdown`) have some kind of try-repeat logic
   * already built into them.  I think in general `bottomup (try R)` is
   * intended to work the same as `bottomup R`---although obviously in practice
   * that doesn't quite pan out.
   *)
  rewrite_strat (bottomup (try (old_hints normalize))).
Qed.
