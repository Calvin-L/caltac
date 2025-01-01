(*
 * Semi-private definitions that
 *  1) Should not be imported by default by `Require Import CalTac.`
 *  2) Can be explicitly imported by `Require Import CalTac.Util.`
 *)

Require Export Ltac2.Ltac2.

Require Import Lia.

From Hammer Require Import Tactics.

(*
NOTE: Many thanks to Tej Chajed for the implementation of `get_lambda_name`.
https://github.com/tchajed/coq-ltac2-experiments/blob/edc29a4d7fe5bc2662055d1b2e8a74bd272b91c1/src/deex.v#L21
*)
Ltac2 get_lambda_name (x:constr) :=
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.Lambda binder _ => Constr.Binder.name binder
  | _ => None
  end.

Ltac2 rec _any (ops : (unit -> unit) list) : bool :=
  match ops with
  | [] => false
  | op :: rest =>
    if Control.plus
      (fun () => op (); true)
      (fun _ => false)
    then true
    else _any rest
  end.

Ltac2 rec _nf_hyp (h : ident) : unit :=
  let hh := Control.hyp h in
  lazy_match! (Constr.type hh) with
  | _ /\ _ =>
    let h2 := Fresh.in_goal @H in
    destruct $hh as [$h $h2] > [_nf_hyp h] > [_nf_hyp h2]
  | ex ?p =>
    match get_lambda_name p with
    | None => destruct $hh as [? $h]
    | Some x => let name := Fresh.in_goal x in destruct $hh as [$name $h]
    end > [_nf_hyp h]
  | True => clear $h
  | _ =>
    if _any [
      (fun () => progress ( cbv beta iota zeta in $h ));
      (fun () => progress ( ltac1:(x |- autounfold with nf in x) (Ltac1.of_ident h) ));
      (fun () => progress ( ltac1:(x |- rewrite_strat (outermost (old_hints nf)) in x) (Ltac1.of_ident h) ))]
    then _nf_hyp h
    else ()
  end.

Ltac2 _nf_all_hyps () : unit :=
  let hyps := Control.hyps () in
  List.iter _nf_hyp (List.map (fun (h, _, _) => h) hyps).

Ltac2 rec _nf_goal () : unit :=
  lazy_match! goal with
  | [ |- forall _, _ ] =>
    intros > [_nf_goal ()]
  | [ |- _ ] =>
    if _any [
      (fun () => progress ( cbv beta iota zeta ));
      (fun () => progress ( ltac1:(autounfold with nf) ));
      (fun () => progress ( ltac1:(rewrite_strat (outermost (old_hints nf))) ))]
    then _nf_goal ()
    else ()
  end.

Ltac2 rec _use (terms : Std.reference list) :=
  match terms with
  | a :: t =>
    let term := Env.instantiate a in
    refine open_constr:((fun _ => _) $term); _use t
  | [] => ()
  end.

Ltac2 _sauto () := ltac1:(sauto limit:100).
Ltac2 Notation "sauto" := _sauto ().

Ltac2 _hauto () := ltac1:(hauto).
Ltac2 Notation "hauto" := _hauto ().

Ltac2 _best () := ltac1:(best).
Ltac2 Notation "best" := _best ().

Ltac solve1 := solve [ eauto | simple congruence | lia ].

(*
 * This defines how CalTac uses CoqHammer.  It's probably not obvious why this
 * set of options is right, so here are some reminders:
 *
 * In general, we want to restrict `obvious` to only what it sees in the proof
 * context.  No chasing inversion/construction rabbit holes, no unfolding big
 * definitions.  This has two benefits:
 *   - First, it makes `obvious` run faster.
 *   - Second, it makes `obvious` less succeptible to definition changes, since
 *     it doesn't "see" into definitions or types.
 *
 * `sauto` is the strongest CoqHammer tactic, and it takes many options.
 *
 * `hauto` is `sauto` with `inv:-` (automatic inversion enabled ONLY for
 * simple logical connectives) and `ctrs:-` (only try applying constructors for
 * simple logical connectives).
 *
 * Additionally we add `red:-` to disable term reduction.  This prevents the
 * tactic from unfolding fixpoints applied to constructors.
 *)
Ltac2 _preferred_hammer_tactic () :=
  ltac1:(hauto red:off urew:off).

(*Ltac2 _obvious () := solve [ ltac1:(firstorder solve1) ].*)
Ltac2 _obvious () := solve [
  _preferred_hammer_tactic () |
  ltac1:(intuition solve1) ].

Lemma modus_ponens:
  forall P Q : Prop,
    (P -> Q) ->
    P ->
    Q.
Proof.
  auto.
Qed.

Ltac2 _suffices (p : constr) := apply (modus_ponens $p) > [ intro | ].

Ltac2 _deduce (p : constr) (t : unit -> unit) := assert $p by (t ()).

Ltac2 _assert (p : constr) (x : ident) (t : unit -> unit) :=
  assert $p as $x by (t ()).

Ltac2 rec break_or (h : ident) :=
  let h_constr := Control.hyp h in
  match! Constr.type h_constr with
  | (_ \/ _) => destruct $h_constr as [$h|$h] > [break_or h | break_or h]
  | _ => ()
  end.

Ltac2 _cases (p : constr) :=
  let hypname := Fresh.in_goal ident:(H) in
  _assert p hypname _obvious > [break_or hypname].

Ltac2 _pick (x : ident) (t : constr) (p : unit -> constr) :=
  let hypname := Fresh.in_goal ident:(H) in
  (assert (ex ltac2:(Control.refine (fun () => Constr.in_context
      (* formal parameter *) x
      (* parameter type *)   t
      (* function body *)    (fun () => Control.refine p))))
      as $hypname
      by (_obvious ()));
  let hh := Control.hyp hypname in
    destruct $hh as [$x $hypname].

Ltac2 _pick_unknown_type (x : ident) (p : unit -> constr) :=
  _pick x open_constr:(_) p.

Ltac2 _case_analysis_step () :=
  lazy_match! goal with
  | [ h : _ \/ _ |- _ ] => let hh := Control.hyp h in destruct $hh
  | [ |- _ <-> _ ] => split
  | [ |- _ /\ _ ] => split
  | [ |- context [ match ?x with _ => _ end ] ] => destruct $x eqn:?
  | [ h : context [ match ?x with _ => _ end ] |- _ ] => destruct $x eqn:?
  | [ |- _ ] => progress (_nf_goal (); _nf_all_hyps ())
  end.
