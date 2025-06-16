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

Definition Δ {V : Set} (f : value V) : value V :=
  v_lam (* x *)
    (e_app (e_value (shift f))
           (v_lam (* y *)
              (e_app (e_app (v_var (VS VZ) (* x *))
                            (v_var (VS VZ) (* x *)))
                     (v_var VZ (* y *))))).

Definition Y : value ∅ := v_lam (e_app (Δ (v_var VZ)) (Δ (v_var VZ))).

Definition θ {V : Set} (ϑ : value V) : value V :=
  v_lam (* f *)
    (e_app (v_var VZ (* f *))
           (v_lam (* y *)
              (e_app (e_app (e_app (e_value (shift (shift ϑ)))
                                   (e_value (shift (shift ϑ))))
                            (v_var (VS VZ) (* f *)))
                     (v_var VZ (* y *))))).

Definition Θ : value ∅ := θ (v_lam (θ (v_var VZ))).

Definition θf (f : value ∅) :=
  e_app f (v_lam (* y *)
              (e_app (e_app (e_app (v_lam (θ (v_var VZ)))
                                   (v_lam (θ (v_var VZ))))
                            (e_value (shift f)))
                     (v_var VZ (* y *)))).

Example fixpoint_equiv n : n ⊨ RelV Y Θ.
Proof.
  apply RelV_intro; iintros f₁ f₂ Hf.
  eapply RelR_red_both;
    [ unfold Y; auto_red
    | unfold Θ; unfold θ at 1; auto_red
    | term_simpl; later_shift ].
  change (n ⊨ RelE (e_app (Δ f₁) (Δ f₁)) (θf f₂)).
  loeb_induction.
  iintros E₁ E₂ HE.
  eapply Obs_red_l; [ auto_red | term_simpl ].
  iapply RelV_elim; [ assumption | | iintro; assumption ].
  clear E₁ E₂ HE.
  later_shift.
  apply RelV_intro; iintros v₁ v₂ Hv.
  eapply RelR_red_both; [ auto_red | auto_red | term_simpl; iintro ].
  iintros E₁ E₂ HE.
  eapply Obs_red_r; [ auto_red | term_simpl ].
  eapply Obs_red_r; [ auto_red | term_simpl ].
  change (n ⊨ Obs (plug E₁ (e_app (e_app (Δ f₁) (Δ f₁)) v₁))
                  (plug E₂ (e_app (θf f₂) v₂))).
  eapply RelE_elim with (E₁ := (ectx_app1 _ _)) (E₂ := (ectx_app1 _ _));
    [ assumption | ].
  apply RelK_intro; iintros u₁ u₂ Hu; simpl.
  iapply RelV_elim; [ assumption | | ]; iintro; assumption.
Qed.
