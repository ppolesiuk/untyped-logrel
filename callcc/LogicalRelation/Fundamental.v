Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.DefUnroll.
Require Import ReductionTactics.

Section LogicalRelation.
Context {ObsCl : ObsClass}.

Lemma RelR_red_both (e₁ e₁' e₂ e₂' : expr ∅) n :
  pure_red e₁ e₁' → pure_red e₂ e₂' →
  n ⊨ ▷ RelE e₁' e₂' →
  n ⊨ RelR e₁ e₂.
Proof.
  intros Hred₁ Hred₂ He; iintros E₁ E₂ HE.
  eapply Obs_red_both.
  + apply red_in_ectx; eassumption.
  + apply red_in_ectx; eassumption.
  + later_shift; iapply He; assumption.
Qed.

(* ========================================================================= *)
(** Compatibility lemmas *)

(* ========================================================================= *)
(* expressions *)

Lemma rel_e_compat_value {V : Set} (v₁ v₂ : value V) n :
  n ⊨ rel_v v₁ v₂ →
  n ⊨ rel_e v₁ v₂.
Proof.
  intro Hv; iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  apply RelK_elim; [ assumption | ].
  iapply Hv; assumption.
Qed.

Lemma rel_e_compat_app {V : Set} (e₁ e₂ e₁' e₂' : expr V) n :
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_e e₁' e₂' →
  n ⊨ rel_e (e_app e₁ e₁') (e_app e₂ e₂').
Proof.
  intros He He'.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  apply RelE_elim with (E₁ := ectx_app1 _ _) (E₂ := ectx_app1 _ _);
    [ iapply He; assumption | ].
  apply RelK_intro; iintros v₁ v₂ Hv.
  apply RelE_elim with (E₁ := ectx_app2 _ _) (E₂ := ectx_app2 _ _);
    [ iapply He'; assumption | ].
  apply RelK_intro; iintros u₁ u₂ Hu; simpl.
  iapply RelV_elimE; assumption.
Qed.

Lemma rel_e_compat_callcc {V : Set} (e₁ e₂ : expr (inc V)) n :
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_e (e_callcc e₁) (e_callcc e₂).
Proof.
  intro He.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift.
  unfold subst; repeat rewrite bind_bind_comp'.
  iapply He; [ | eassumption ].
  iintro x; destruct x as [ | x ]; term_simpl; [ | iapply Hγ ].
  apply RelV_intro; iintros u₁ u₂ Hu F₁ F₂ HF.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  apply RelK_elim; assumption.
Qed.

Lemma rel_e_compat_abort {V : Set} (p₁ p₂ : program V) n :
  n ⊨ rel_p p₁ p₂ →
  n ⊨ rel_e (e_abort p₁) (e_abort p₂).
Proof.
  intro Hp.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl.
  eapply Obs_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  iapply Hp; assumption.
Qed.

Lemma rel_e_compat_fmap {A B : Set} (f : A [→] B) e₁ e₂ n :
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_e (fmap f e₁) (fmap f e₂).
Proof.
  intro He.
  iintros γ₁ γ₂ Hγ.
  repeat rewrite (map_to_bind f), bind_bind_comp'.
  iapply He.
  iintro x; iapply Hγ.
Qed.

Lemma rel_e_compat_bind {A B : Set} (f₁ f₂ : A [⇒] B) e₁ e₂ n :
  n ⊨ (∀ᵢ x, rel_v (f₁ x) (f₂ x)) →
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_e (bind f₁ e₁) (bind f₂ e₂).
Proof.
  intros Hf He.
  iintros γ₁ γ₂ Hγ.
  repeat rewrite bind_bind_comp'.
  iapply He.
  iintro x; iapply Hf; assumption.
Qed.

(* ========================================================================= *)
(* values *)

Lemma rel_v_compat_var {V : Set} (x : V) n :
  n ⊨ rel_v (v_var x) (v_var x).
Proof.
  iintros γ₁ γ₂ Hγ; iapply Hγ.
Qed.

Lemma rel_v_compat_lam {V : Set} (e₁ e₂ : expr (inc V)) n :
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_v (v_lam e₁) (v_lam e₂).
Proof.
  intro He;
  iintros γ₁ γ₂ Hγ; term_simpl.
  apply RelV_intro; iintros u₁ u₂ Hu.
  eapply RelR_red_both; [ auto_red | auto_red | ]; later_shift; term_simpl.
  unfold subst; repeat rewrite bind_bind_comp'.
  iapply He.
  iintro x; destruct x as [ | x ]; term_simpl.
  + assumption.
  + iapply Hγ.
Qed.

(* ========================================================================= *)
(* programs *)

Lemma rel_p_compat_expr {V : Set} (e₁ e₂ : expr V) n :
  n ⊨ rel_e e₁ e₂ →
  n ⊨ rel_p e₁ e₂.
Proof.
  intro He.
  iintros γ₁ γ₂ Hγ; term_simpl.
  apply RelE_elim with (E₁ := ectx_hole) (E₂ := ectx_hole).
  + iapply He; assumption.
  + apply RelK_intro; iintros v₁ v₂ Hv; apply Obs_value.
Qed.

(* ========================================================================= *)
(** Fundamental Property *)

Fixpoint fundamental_property_e {V : Set} (e : expr V) n :
  n ⊨ rel_e e e
with fundamental_property_v {V : Set} (v : value V) n :
  n ⊨ rel_v v v
with fundamental_property_p {V : Set} (p : program V) n :
  n ⊨ rel_p p p.
Proof.
+ destruct e.
  - apply rel_e_compat_value, fundamental_property_v.
  - apply rel_e_compat_app; apply fundamental_property_e.
  - apply rel_e_compat_callcc, fundamental_property_e.
  -  apply rel_e_compat_abort, fundamental_property_p.
+ destruct v.
  - apply rel_v_compat_var.
  - apply rel_v_compat_lam, fundamental_property_e.
+ destruct p.
  - apply rel_p_compat_expr, fundamental_property_e.
Qed.

Lemma precongruence {V : Set} (e₁ e₂ : expr V) C n :
  n ⊨ rel_e e₁ e₂ → n ⊨ rel_p (cplug C e₁) (cplug C e₂).
Proof.
  revert e₁ e₂ n; induction C; intros e₁ e₂ n He; simpl; try apply IHC.
  + apply rel_p_compat_expr; assumption.
  + apply rel_e_compat_fmap; assumption.
  + apply rel_e_compat_bind; [ | assumption ].
    iintro; apply fundamental_property_v.
  + apply rel_e_compat_value, rel_v_compat_lam; assumption.
  + apply rel_e_compat_app; [ assumption | ]; apply fundamental_property_e.
  + apply rel_e_compat_app; [ | assumption ]; apply fundamental_property_e.
  + apply rel_e_compat_callcc; assumption.
  + apply rel_e_compat_abort, rel_p_compat_expr; assumption.
Qed.

End LogicalRelation.
