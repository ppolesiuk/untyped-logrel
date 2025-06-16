Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common ReductionTactics.
Require Import Translation.Inverse.
Require Import MixedLogicalRelation.MObs.
Require Import MixedLogicalRelation.Core.
Require Import MixedLogicalRelation.DefUnroll.

Fixpoint mrel_e_uncps {Δ : T.VCtx} (e : T.expr Δ) n :
  n ⊨ mrel_e Δ (expr_uncps e) e
with mrel_v_uncps {κ : T.kind} {Δ : T.VCtx} (v : T.valuelike κ Δ) n :
  n ⊨ mrel_vk Δ (value_uncps v) v
with mrel_p_uncps {Δ : T.VCtx} (p : T.program Δ) n :
  n ⊨ mrel_p Δ (program_uncps p) p.
Proof.
{ destruct e; simpl.
  + iintros γ₁ γ₂ Hγ E k HEk; term_simpl.
    eapply MObs_red_l; [ auto_red | ]; term_simpl.
    eapply MObs_red_l; [ auto_red | ].
    eapply MObs_red_r; [ constructor | ].
    unfold subst; repeat rewrite bind_bind_comp'.
    iapply mrel_p_uncps.
    iintro x; destruct x; term_simpl; [ | iapply Hγ ].
    iintros v₁ v₂ Hv; simpl.
    eapply MObs_red_l; [ auto_red | ]; term_simpl.
    eapply MObs_red_l; [ auto_red | ].
    iapply HEk; assumption.
  + iintros γ₁ γ₂ Hγ; term_simpl.
    apply MRelV_elimE; iapply (mrel_v_uncps T.k_val); assumption.
}
{ destruct v as [ κ x EQ | | ]; simpl.
  + iintros γ₁ γ₂ Hγ; term_simpl.
    destruct EQ; iapply Hγ.
  + iintros γ₁ γ₂ Hγ; term_simpl.
    apply MRelV_intro; iintros v₁ v₂ Hv E k HEk.
    eapply MObs_red_both; [ auto_red | constructor | ]; term_simpl.
    later_shift.
    unfold subst; repeat rewrite bind_bind_comp'.
    iapply mrel_e_uncps; [ | assumption ].
    iintro x; destruct x; term_simpl; [ assumption | iapply Hγ ].
  + iintros γ₁ γ₂ Hγ; term_simpl.
    apply MRelK_intro; iintros v₁ v₂ Hv; simpl.
    eapply MObs_red_l; [ auto_red | ]; term_simpl.
    eapply MObs_red_r; [ constructor | ].
    unfold subst; repeat rewrite bind_bind_comp'.
    iapply mrel_p_uncps.
    iintro x; destruct x; term_simpl; [ assumption | iapply Hγ ].
}
{ destruct p; simpl.
  + iintros γ₁ γ₂ Hγ; term_simpl; apply MObs_value.
  + iintros γ₁ γ₂ Hγ; term_simpl.
    apply MRelE_elim with (E := S.ectx_app2 _ S.ectx_hole).
    - iapply mrel_e_uncps; assumption.
    - iapply (mrel_v_uncps T.k_cont); assumption.
  + iintros γ₁ γ₂ Hγ; term_simpl.
    apply MRelK_elim with (E := S.ectx_app2 _ S.ectx_hole).
    - iapply (mrel_v_uncps T.k_cont); assumption.
    - iapply (mrel_v_uncps T.k_val); assumption.
}
Qed.

Lemma uncps_preserves_termination (p : T.program mtC) :
  S.terminates (program_uncps p) ↔ T.terminates p.
Proof.
  apply MObs_adequacy; intro n.
  rewrite <- (bind_pure' p) at 2; rewrite <- (bind_pure' (program_uncps p)).
  iapply mrel_p_uncps; iintro x; destruct x.
Qed.

Lemma uncps_preserves_obs_equiv p₁ p₂ :
  T.obs_equiv p₁ p₂ ↔ S.obs_equiv (program_uncps p₁) (program_uncps p₂).
Proof.
  unfold S.obs_equiv.
  repeat rewrite uncps_preserves_termination.
  reflexivity.
Qed.

(* ========================================================================= *)

Fixpoint program_uncps_plugE {Δ : T.VCtx} (C : T.ctxE Δ) e :
  S.p_expr (program_uncps (T.plugE C e)) =
  S.cplug (ctxE_uncps C) (expr_uncps e)

with program_uncps_plugV {Δ : T.VCtx} (C : T.ctxV Δ) v :
  S.p_expr (program_uncps (T.plugV C v)) =
  S.cplug (ctxV_uncps C) (value_uncps v)

with program_uncps_plugK {Δ : T.VCtx} (C : T.ctxK Δ) k :
  S.p_expr (program_uncps (T.plugK C k)) =
  S.cplug (ctxK_uncps C) (value_uncps k)

with program_uncps_plugP {Δ : T.VCtx} (C : T.ctxP Δ) p :
  S.p_expr (program_uncps (T.plugP C p)) =
  S.cplug (ctxP_uncps C) (program_uncps p).
Proof.
{ destruct C; term_simpl.
  + erewrite expr_uncps_fmap; [ apply program_uncps_plugE | reflexivity ].
  + erewrite expr_uncps_bind; [ apply program_uncps_plugE | ].
    intros x κ EQ; simpl; subst; reflexivity.
  + apply program_uncps_plugV.
  + apply program_uncps_plugP.
}
{ destruct C; term_simpl.
  + erewrite value_uncps_fmap; [ apply program_uncps_plugV | reflexivity ].
  + apply program_uncps_plugE.
  + apply program_uncps_plugE.
  + apply program_uncps_plugP.
  + apply program_uncps_plugP.
}
{ destruct C; term_simpl.
  + apply program_uncps_plugP.
  + apply program_uncps_plugP.
}
{ destruct C; term_simpl.
  + reflexivity.
  + apply program_uncps_plugE.
  + apply program_uncps_plugK.
}
Qed.

(* ========================================================================= *)

Require Import Translation.Core.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.DefUnroll.
Require Import LogicalRelation.Fundamental.
Require Import EquivLogicalRelation.Obs.
Require Import EquivLogicalRelation.SoundnessAndCompleteness.

Local Ltac logrel_red_l :=
  repeat (eapply Obs_red_l; [ auto_red; fail | ]; term_simpl);
  change Obs with Core.Obs.

Local Ltac logrel_red_r :=
  eapply Obs_red_r; [ auto_red | ]; term_simpl;
  change Obs with Core.Obs.

Fixpoint expr_cps_inv_log {Δ : T.VCtx}
    (H : value_VCtx Δ) (e : S.expr (dom Δ)) n :
  n ⊨ rel_e (expr_uncps (expr_cps H e)) e
with value_cps_inv_log {Δ : T.VCtx}
    (H : value_VCtx Δ) (v : S.value (dom Δ)) n :
  n ⊨ rel_v (value_uncps (value_cps H v)) v
with program_cps_inv_log {Δ : T.VCtx}
    (H : value_VCtx Δ) (p : S.program (dom Δ)) n :
  n ⊨ rel_p (program_uncps (program_cps H p)) p.
Proof.
{ destruct e; simpl.
  + rewrite value_uncps_shift.
    iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl; logrel_red_l.
    apply RelK_elim; [ assumption | ].
    iapply value_cps_inv_log; assumption.
  + repeat rewrite expr_uncps_shift.
    iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl; logrel_red_l.
    apply RelE_elim with (E₁ := S.ectx_app2 _ S.ectx_hole)
                         (E₂ := S.ectx_app1 _ _);
      [ iapply expr_cps_inv_log; assumption | ].
    apply RelK_intro; iintros v₁ v₂ Hv; simpl; logrel_red_l.
    apply RelE_elim with (E₁ := S.ectx_app2 _ S.ectx_hole)
                         (E₂ := S.ectx_app2 _ _);
      [ iapply expr_cps_inv_log; assumption | ].
    apply RelK_intro; iintros u₁ u₂ Hu; simpl; logrel_red_l.
    apply RelE_elim with (E₁ := S.ectx_app2 _ S.ectx_hole);
      [ apply RelV_elimE; assumption | ].
    apply RelK_intro; iintros w₁ w₂ Hw; simpl; logrel_red_l.
    apply RelK_elim; assumption.
  + erewrite <- expr_uncps_fmap;
      [ | instantiate (1 := lift mk_shift); reflexivity ].
    iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl; logrel_red_l; logrel_red_r.
    rewrite (map_to_bind (lift mk_shift)).
    unfold subst; repeat rewrite bind_bind_comp'.
    apply RelE_elim with (E₁ := S.ectx_app2 _ S.ectx_hole).
    - iapply expr_cps_inv_log.
      iintro x; destruct x as [ | x ]; term_simpl.
      * apply RelV_intro; iintros u₁ u₂ Hu F₁ F₂ HF.
        eapply Obs_red_both; [ auto_red | auto_red | ]; term_simpl.
        later_shift; logrel_red_l; logrel_red_r.
        apply RelK_elim; assumption.
      * unfold shift.
        repeat rewrite (map_to_bind mk_shift).
        repeat rewrite bind_bind_comp'.
        rewrite bind_pure; [ iapply Hγ | ].
        intros [].
    - apply RelK_intro; iintros v₁ v₂ Hv; simpl; logrel_red_l.
      apply RelK_elim; assumption.
  + rewrite program_uncps_shift.
    iintros γ₁ γ₂ Hγ E₁ E₂ HE; term_simpl; logrel_red_l.
    eapply Obs_red_r; [ auto_red | ]; term_simpl.
    iapply program_cps_inv_log; assumption.
}
{ destruct v; simpl.
  + apply rel_v_compat_var.
  + apply rel_v_compat_lam. apply (@expr_cps_inv_log (extC _ _)).
}
{ destruct p; simpl.
  iintros γ₁ γ₂ Hγ; term_simpl.
  change Obs with Core.Obs.
  apply RelE_elim with (E₁ := S.ectx_app2 _ S.ectx_hole) (E₂ := S.ectx_hole);
    [ iapply expr_cps_inv_log; assumption | ].
  apply RelK_intro; iintros v₁ v₂ Hv.
  logrel_red_l; apply Obs_value.
}
Qed.

Lemma expr_cps_inv_ctx {Δ : T.VCtx}
    (H : value_VCtx Δ) (e : S.expr (dom Δ)) :
  S.ctx_equiv (expr_uncps (expr_cps H e)) e.
Proof.
  apply rel_e_soundness; intro n.
  apply expr_cps_inv_log.
Qed.

Lemma program_cps_inv_obs p :
  S.obs_equiv (program_uncps (program_cps value_VCtx_mtC p)) p.
Proof.
  apply Obs_adequacy; intro n.
  rewrite <- (bind_pure' p) at 2; rewrite <- (bind_pure' (program_uncps _)).
  iapply program_cps_inv_log.
  iintro x; destruct x.
Qed.
