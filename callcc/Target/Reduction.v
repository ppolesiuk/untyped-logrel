Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import Target.Syntax.
Require Import Relation_Operators.

Inductive red {V : VCtx} : program V → program V → Prop :=
| red_betaE : ∀ p k,
    red (p_appE (e_lam p) k) (subst (F:=cont) p k)

| red_betaV : ∀ e v k,
    red (p_appE (e_app (v_vlam e) v) k) (p_appE (subst (F:=value) e v) k)

| red_betaK : ∀ p v,
    red (p_appK (v_clam p) v) (subst (F:=value) p v)
.

Notation red_rtc e₁ e₂ := (clos_refl_trans_1n _ red e₁ e₂).

Definition terminates {V : VCtx} (p : program V) :=
  ∃ v : value V, red_rtc p (p_value v).
