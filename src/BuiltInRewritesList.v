Require Import List.
Require Import CalTac.Core.
Require Import CalTac.BuiltInRewritesProp.

(* ---- ++ ---- *)

#[export] Hint Rewrite app_nil_l : nf.
#[export] Hint Rewrite app_nil_r : nf.

(* ---- In ---- *)

Lemma in_nil_iff:
  forall T (x : T),
    In x nil <-> False.
Proof.
  unfold In; obvious.
Qed.
#[export] Hint Rewrite in_nil_iff : nf.

Lemma in_cons_iff:
  forall T (x y : T) l,
    In x (cons y l) <-> (x = y \/ In x l).
Proof.
  unfold In; obvious.
Qed.
#[export] Hint Rewrite in_cons_iff : nf.

#[export] Hint Rewrite in_app_iff : nf.

(* ---- length ---- *)

Lemma length_nil:
  forall T,
    @length T nil = 0.
Proof.
  unfold length; obvious.
Qed.
#[export] Hint Rewrite length_nil : nf.

Lemma length_cons:
  forall T (x : T) l,
    length (x :: l) = S (length l).
Proof.
  unfold length; obvious.
Qed.
#[export] Hint Rewrite length_cons : nf.

#[export] Hint Rewrite length_app : nf.
#[export] Hint Rewrite length_map : nf.

(* ---- map ---- *)

Lemma map_nil:
  forall T U (f : T -> U),
    map f nil = nil.
Proof.
  unfold map; obvious.
Qed.
#[export] Hint Rewrite map_nil : nf.
#[export] Hint Rewrite map_cons : nf.
#[export] Hint Rewrite map_app : nf.
#[export] Hint Rewrite in_map_iff : nf.

(* ---- filter ---- *)

Lemma filter_nil:
  forall T (f : T -> bool),
    filter f nil = nil.
Proof.
  unfold filter; obvious.
Qed.
#[export] Hint Rewrite filter_nil : nf.

Lemma filter_cons:
  forall T (f : T -> bool) x l,
    filter f (x :: l) = (if f x then cons x nil else nil) ++ filter f l.
Proof.
  unfold filter; obvious.
Qed.
#[export] Hint Rewrite filter_cons : nf.

#[export] Hint Rewrite filter_app : nf.

Lemma in_filter_iff:
  forall T (f : T -> bool) x l,
    In x (filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; nf; obvious.
Qed.
#[export] Hint Rewrite in_filter_iff : nf.
