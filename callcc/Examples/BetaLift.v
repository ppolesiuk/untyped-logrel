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

(** Reduction β_lift from Figure 1 of Reasoning about Programs in
  * Continuation-Passing Style, Amr Sabry and Matthias Felleisen, 1993. *)
Example beta_lift {V : Set}
    (E : rctx V) (e₁ : expr (inc V)) (e₂ : expr V) :
  ctx_equiv (rplug E (e_app (v_lam e₁) e₂))
            (e_app (v_lam (rplug (shift E) e₁)) e₂).
Proof.
  apply rel_e_soundness; intro n.
  iintros γ₁ γ₂ Hγ; term_simpl.
  iintros E₁ E₂ HE.
  rewrite <- ectx_comp_plug.
  apply RelE_elim with (E₁ := ectx_app2 _ _) (E₂ := ectx_app2 _ _);
    [ iapply fundamental_property_e; assumption | ].
  iintros v₁ v₂ Hv.
  eapply Obs_red_both; [ auto_red | auto_red | later_shift ].
  rewrite ectx_comp_plug.
  apply RelE_elim; [ | assumption ].
  erewrite <- (subst_shift_id (bind γ₁ E)), <- subst_rplug.
  repeat rewrite <- bind_liftS_shift_comm, <- bind_rplug.
  unfold subst; repeat rewrite bind_bind_comp'.
  iapply fundamental_property_e.
  iintros [ | x ]; term_simpl; [ | iapply Hγ ].
  apply RelV_unroll; assumption.
Qed.
