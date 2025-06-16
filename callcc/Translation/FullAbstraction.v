Require Import Utf8.
Require Import Common.
Require Import Translation.Core Translation.Properties.
Require Import Translation.Inverse Translation.InverseProperties.

Theorem full_abstraction {V : Set} (e₁ e₂ : S.expr V) :
  S.ctx_equiv e₁ e₂ ↔
  T.ctx_equiv (expr_cps value_VCtx_cps e₁) (expr_cps value_VCtx_cps e₂).
Proof.
  split; intros Hequiv C.
  + apply uncps_preserves_obs_equiv.
    repeat rewrite program_uncps_plugE.
    etransitivity; [ apply expr_cps_inv_ctx | ].
    etransitivity; [ | symmetry; apply expr_cps_inv_ctx ].
    apply Hequiv.
  + etransitivity; [ symmetry; apply program_cps_inv_obs | ].
    etransitivity; [ | apply program_cps_inv_obs ].
    apply uncps_preserves_obs_equiv.
    repeat rewrite program_cps_cplug.
    apply Hequiv.
Qed.
