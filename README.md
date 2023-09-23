# Calvin's Tactics

A highly-opinionated set of Coq tactics.  (Just looking for a high-level
overview?  Jump ahead to "Usage and Core Tactics" below.)

```coq
Require Import CalTac.CalTac.

Lemma strong_induction:
  forall P : nat -> Prop,
    (forall n, (forall m, m < n -> P m) -> P n) ->
    (forall x, P x).
Proof.

  nf.
  suffices (forall m, m < x -> P m) by obvious.
  induction x; nf.

  - suffices (~(m < 0)) by obvious.
    obvious.

  - assert (m <= x) by obvious.
    cases (m < x \/ m = x).
    + obvious.
    + obvious.

Qed.
```


## Motivation

This is a tactics library designed to produce readable proofs.  Readability is
hard to measure, but I hypothesize that a proof script is more readable if it
explicitly declares the outcome of each step rather than simply naming the
action to be performed.

Consider the difference between:

    (1)   apply lemma.
    (2)   suffices (x = 0) by obvious using lemma.

The "traditional" Coq style of proof is represented by (1), an action that
modifies the goal.  This library instead encourages (2), a statement of the new
goal and a hint for Coq about how to get there.

I did not say this library helps produce COMPACT proofs.  While I'm sure there
is some relationship between compactness and readability, compactness is not a
goal of this library.  In fact, most proofs written with this library will be
MORE verbose than they would have been otherwise.  However, the extra verbosity
is usually restatements of the goal and statements of various intermediate
conclusions---which are useful when trying to read or repair a proof.


## Installation

`make install`


## Usage and Core Tactics

`Require Import CalTac.CalTac.`

  - `nf.`
    Convert the current goal and context to "normal form" (nf).  Normal form is
    a little easier to read and work with.  Calling `nf` will never close a
    goal or generate new ones.  These are the rules:
      - `(H : A /\ B) |- _`          ==>   `H1:A, H2:B |- _`
      - `(H : exists x, P x) |- _`   ==>   `x, P x |- _`
      - `|- forall x, P x`           ==>   `x |- P x`
      - `|- P -> Q`                  ==>   `P |- Q`
      - `(fun x => P) y`             ==>   `P[x |-> y]`       ("beta" reduction)
      - `let a := b in c`            ==>   `c[a |-> b]`       ("zeta" reduction)
      - `match A with A => B end`    ==>   `B`                ("match" reduction)
      - any unfolding rule in the hint database `nf`
      - any rewrite rule in the rewrite hint database `nf`

  - `obvious [using lem1, lem2, ...].`
    Immediately prove the current goal using a battery of quick solver tactics.
    The names of additional lemmas can be provided; these will be added to the
    context as extra hypotheses before invoking the solver tactics.

  - `suffices (P). { proof }`
    Changes the goal to P ("backward" reasoning).  The given proof must show
    that `P |- goal`.  As a common shorthand, you can also write
    `suffices (P) by obvious.`

  - `cases (P1 \/ P2 \/ ... \/ Pn).`
    Case analysis: break the proof into subgoals (one assuming P1, one assuming
    P2, etc).  Leverages `obviously` to deduce `(P1 \/ ... \/ Pn)`---i.e. that
    no cases have been missed.

In addition, there are a number of tactics from the Coq standard library that
I think fit well into the proof style this library encourages:

  - `assert (P). { proof }`
    Deduce P manually ("forward" reasoning).


## Prototype Tactics

  `pick x [: T] st P.`
    Extend the context with `(x:T)` and `(_:P)`.  Leverages `obviously` to
    prove `exists x:T, P`.  This is useful if you need to assign a name to some
    important term.

  `case_analysis.`
    Automatically break the goal up into subgoals.  Disjunctions get
    destructed, the targets of `match` expressions get destructed, and goals
    for `/\` and `<->` get split.  This tactic will also do everything that
    `nf` does.


## Advanced Usage

Classical logicians like me can use `Require Import CalTac.Classical.`  That
adds some useful classical rewrites to `nf` and re-exports Coq's classical
lemma libraries.  Your proofs will end up depending on the [axiom of the
excluded middle](https://coq.inria.fr/library/Coq.Logic.Classical_Prop.html#classic).

On the other end of the spectrum, `Require Import CalTac.Core.` will import
the tactics only, without any rewrite rules.


## Tips and Tricks

### What is `obvious` to CalTac?

It's a bit fuzzy, but you can rely on:

  - **Assumptions are true.**  If your goal appears in the context, then it's
    `obvious`.
  - **Syntactic reflexivity.**  Syntactically equal terms are equal.
  - **Contradictions.**  If `P` and `~P` are both in the context, then any goal
    is `obvious`.
  - **Instantiation/deduction.**  If `forall x, P x` is in the context, then
    `P any_other_term` is `obvious`.  Similarly if `P -> Q` and `P` are both
    in the context, then `Q` is `obvious`.
  - **Simple arithmetic.**  Basic arithmetic facts like `x<4 -> x<(5+5)` are
    `obvious`.

Note that `obvious` is _deliberately limited_ in some ways:

  - **Limited (or no) unfolding.**  In general, a goal is only `obvious` if
    everything required to prove it appears in the context.  The tactic does
    not unfold or invert anything on your behalf, and in particular it often
    does not recognize definitionally-equal terms as equal unless they are also
    syntactically-equal.  You may need to prove additional lemmas to supply
    `obvious` with the facts it needs.  Someday I'll write a long article about
    why this is the right approach.
  - **Reasoning is not transitive.**  If your proof requires instantiation
    followed by arithmetic, `obvious` may not be able to chain both reasoning
    steps together, even if it can do each individually.


### "Unfolding" Lemmas and Simplification Rewrites

Ideally, most of your proofs will look like

```coq
induction x;
  nf;
  obvious using lemma1, lemma2.
```

To realize this dream, I recommend the style endorsed by Olivier Danvy in
[Fold–unfold lemmas for reasoning about recursive programs using the Coq proof
assistant](https://dx.doi.org/10.1017/S0956796822000107).

Because `obvious` does not unfold definitions, it can be helpful to prove
"unfolding" lemmas:

```coq
Definition foo x := ...
Lemma unfold_foo: forall x, foo x = <body_of_foo>. ... Qed.
```

This can be especially useful because if `foo` is recursive, Coq cannot reduce
`foo x` unless `x` is a constructor.  Unfolding lemmas enable this.

In addition, your proof efforts can be drastically simplified using
simplification rewrites:

```coq
Lemma add_x_0: forall x, x + 0 = x. ... Qed.
#[export] Hint Rewrite add_x_0 : nf.
```

For best results, do not add rewrite rules with preconditions to the rewrite
database.


### Getting used to Ltac2

This library uses Ltac2, and importing it will change your proof mode to Ltac2.

You will often need parentheses in more places than you would in legacy Ltac:

    try obvious.    (* fails *)
    try (obvious).  (* works! *)

    repeat rewrite S.read_write.    (* fails with confusing `Error: Unbound value S.read_write` *)
    repeat (rewrite S.read_write).  (* works! *)

Ltac2 is a bit inconsistent about what names in terms refer to.  Sometimes
if you have an `x` in your local context and an `x` in the outer module, you'll
have Ltac2 see the outer one when you want the inner one:

    suffices (x = 0).   (* refers to OUTER x; probably NOT what you want *)
    suffices (&x = 0).  (* refers to INNER x; probably IS what you want *)
