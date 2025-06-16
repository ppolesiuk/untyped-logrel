Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import ApproxLogicalRelation.Obs.
Require Import ApproxLogicalRelation.SoundnessAndCompleteness.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.DefUnroll.
Require Import LogicalRelation.Fundamental.
Require Import ReductionTactics.

Lemma code_dup_l e₁ e₂ n :
  n ⊨ RelE e₁ e₂ → n ⊨ RelE (e_app (v_lam (shift e₁)) e₁) e₂.
Proof.
  intro He.
  iintros E₁ E₂ HE.
  assert (Hobs : n ⊨ Obs (plug E₁ e₁) (plug E₂ e₂)) by
    (iapply He; assumption).
  idestruct Hobs; [ | iright; assumption ].
  apply RelE_elim with (E₁ := ectx_app2 _ E₁); [ assumption | ].
  apply RelK_intro; iintros v₁ v₂ Hv.
  eapply Obs_red_l; [ auto_red | ]; term_simpl; later_shift.
  ileft; assumption.
Qed.

Lemma code_dup_r e₁ e₂ n :
  n ⊨ RelE e₁ e₂ → n ⊨ RelE e₁ (e_app (v_lam (shift e₂)) e₂).
Proof.
  intro He.
  iintros E₁ E₂ HE.
  assert (Hobs : n ⊨ Obs (plug E₁ e₁) (plug E₂ e₂)) by
    (iapply He; assumption).
  idestruct Hobs; [ ileft; assumption | ].
  apply RelE_elim with (E₂ := ectx_app2 _ E₂); [ assumption | ].
  apply RelK_intro; iintros v₁ v₂ Hv.
  eapply Obs_red_r; [ auto_red | ]; term_simpl.
  iright; assumption.
Qed.

Example code_dup {V : Set} (e : expr V) :
  ctx_equiv (e_app (v_lam (shift e)) e) e.
Proof.
  apply ctx_equiv_both_approx; apply rel_e_soundness;
    intro n; iintros γ₁ γ₂ Hγ; term_simpl;
    [ apply code_dup_l | apply code_dup_r ];
    iapply fundamental_property_e; assumption.
Qed.
