Require Import Utf8.
Require Import Target.Syntax.
Require Import Target.Reduction.

Lemma value_do_not_red {Δ : VCtx} (v : value Δ) p :
  ¬ red (p_value v) p.
Proof.
  inversion 1.
Qed.

Lemma red_deterministic {Δ : VCtx} (p p₁ p₂ : program Δ) :
  red p p₁ → red p p₂ → p₁ = p₂.
Proof.
  destruct 1; inversion 1; reflexivity.
Qed.
