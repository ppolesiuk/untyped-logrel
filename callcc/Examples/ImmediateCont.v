Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import EquivLogicalRelation.Obs.
Require Import EquivLogicalRelation.SoundnessAndCompleteness.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.DefUnroll.
Require Import LogicalRelation.Fundamental.
Require Import ReductionTactics.

Lemma immediate_cont_cl (e₁ e₂ : expr ∅) n :
  n ⊨ RelE e₁ e₂ →
  n ⊨ RelE (e_callcc (e_app (v_var VZ) (shift e₁))) e₂.
Proof.
  intro He.
  iintros E₁ E₂ HE.
  eapply Obs_red_l; [ auto_red | term_simpl ].
  change Obs.Obs with Obs.
  apply RelE_elim with (E₁ := ectx_app2 _ E₁); [ assumption | ].
  iintros v₁ v₂ Hv.
  eapply Obs_red_l; [ auto_red | term_simpl ].
  eapply Obs_red_l; [ auto_red | ].
  change Obs.Obs with Obs.
  apply RelK_elim; [ | apply RelV_unroll ]; assumption.
Qed.

Example immediate_cont {V : Set} (e : expr V) :
  ctx_equiv (e_callcc (e_app (v_var VZ) (shift e))) e.
Proof.
  apply rel_e_soundness; intro n.
  iintros γ₁ γ₂ Hγ; term_simpl.
  apply immediate_cont_cl.
  iapply fundamental_property_e; assumption.
Qed.
