Require Export Ltac2.Ltac2.
Require Ltac2.Fresh.
Require Ltac2.Message.
Require Ltac2.Constr.

Require Import CalTac.Internals.

Ltac2 Notation "nf" := repeat (_nf_step ()).

Ltac2 Notation "use" t(list1(reference, ",")) := _use t.

Ltac2 Notation "obvious" := _obvious ().
Ltac2 Notation "obvious" "using" hyps(list1(reference, ",")) := _use hyps; obvious.

Ltac2 Notation "suffices" p(constr) := _suffices p.
Ltac2 Notation "suffices" p(constr) "by" t(thunk(tactic)) := _suffices p > [ t () | ].

Ltac2 Notation "cases" p(constr) := _cases p.

Ltac2 Notation "pick" x(ident) "st" p(thunk(constr)) :=
  _pick_unknown_type x p.
Ltac2 Notation "pick" x(ident) ":" t(constr) "st" p(thunk(constr)) :=
  _pick x t p.

Ltac2 Notation "case_analysis" := repeat (_case_analysis_step ()).
