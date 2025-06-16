Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common.

Definition MObs_sig := S.program ∅ ⇒ᵢ T.program mtC ⇒ᵢ IRel.

Definition F_MObsL (MObsL : MObs_sig) : MObs_sig :=
  λ p₁ p₂,
  (∀ v₁ : S.value ∅, p₁ = v₁ → T.terminates p₂)ᵢ ∧ᵢ
  ∀ᵢ p₁' : S.program ∅, (S.red p₁ p₁')ᵢ →ᵢ ▷ MObsL p₁' p₂.

Definition F_MObsR (MObsR : MObs_sig) : MObs_sig :=
  λ p₁ p₂,
  (∀ v₂ : T.value _, p₂ = (T.p_value v₂) → S.terminates p₁)ᵢ ∧ᵢ
  ∀ᵢ p₂' : T.program _, (T.red p₂ p₂')ᵢ →ᵢ ▷ MObsR p₁ p₂'.

Definition MObsL_fix := I_fix F_MObsL.
Definition MObsR_fix := I_fix F_MObsR.

Notation MObsL := (F_MObsL MObsL_fix).
Notation MObsR := (F_MObsR MObsR_fix).

Definition MObs p₁ p₂ := MObsL p₁ p₂ ∧ᵢ MObsR p₁ p₂.

(* ========================================================================= *)
(* MObsL properties *)

Lemma F_MObsL_contractive : contractive F_MObsL.
Proof.
  intro n; iintros; unfold F_MObsL; auto_contr.
Qed.

Lemma MObsL_roll p₁ p₂ n :
  n ⊨ MObsL p₁ p₂ → n ⊨ MObsL_fix p₁ p₂.
Proof.
  intro H; iapply (I_fix_roll MObs_sig); [ | exact H ].
  apply F_MObsL_contractive.
Qed.

Lemma MObsL_unroll p₁ p₂ n :
  n ⊨ MObsL_fix p₁ p₂ → n ⊨ MObsL p₁ p₂.
Proof.
  intro H; iapply (I_fix_unroll MObs_sig); [ | exact H ].
  apply F_MObsL_contractive.
Qed.

Lemma MObsL_red_l p₁ p₁' p₂ n :
  S.red p₁ p₁' → n ⊨ ▷ MObsL p₁' p₂ → n ⊨ MObsL p₁ p₂.
Proof.
  intros Hred Hp; isplit.
  + iintro; intros v₁ Hv₁; rewrite Hv₁ in Hred.
    exfalso; eapply S.value_do_not_red; eassumption.
  + iintros p Hred2; idestruct Hred2.
    assert (Heq : p = p₁') by
      (eapply S.red_deterministic; eassumption).
    rewrite Heq; later_shift; apply MObsL_roll; assumption.
Qed.

Lemma MObsL_red_r p₂ p₂' n :
  T.red p₂ p₂' → n ⊨ ∀ᵢ p₁, MObsL p₁ p₂' →ᵢ MObsL p₁ p₂.
Proof.
  intro Hred; loeb_induction.
  iintros p₁ Hp; idestruct Hp as Hp_v Hp_red; idestruct Hp_v.
  isplit.
  + iintro; intros v₁ Heq.
    specialize (Hp_v v₁ Heq); destruct Hp_v as [ v₂ Hred_rtc ].
    exists v₂; econstructor; eassumption.
  + iintros p₁' Hred₁; iapply Hp_red in Hred₁; later_shift.
    apply MObsL_roll; iapply IH; apply MObsL_unroll; assumption.
Qed.

Lemma MObsL_value (v₁ : S.value ∅) v₂ n :
  n ⊨ MObsL v₁ (T.p_value v₂).
Proof.
  isplit.
  + iintro; intros; eexists; constructor.
  + iintro p; iintro Hred; idestruct Hred.
    exfalso; eapply S.value_do_not_red; eassumption.
Qed.

Lemma MObsL_adequacy (v₁ : S.value _) p₁ p₂ :
  S.red_rtc p₁ v₁ → (∀ n, n ⊨ MObsL p₁ p₂) → T.terminates p₂.
Proof.
  intro RED; remember (S.p_expr v₁) as p; revert RED Heqp.
  induction 1; intros Hp Hobs.
  + specialize (Hobs {| nw_index := 0 |}).
    apply I_conj_elim1, I_prop_elim in Hobs.
    eapply Hobs; eassumption.
  + apply IHRED; [ assumption | ].
    intro w; specialize (Hobs (world_lift w)).
    apply MObsL_unroll, I_world_lift_later.
    iapply Hobs; iintro; assumption.
Qed.

(* ========================================================================= *)
(* MObsR properties *)

Lemma F_MObsR_contractive : contractive F_MObsR.
Proof.
  intro n; iintros; unfold F_MObsR; auto_contr.
Qed.

Lemma MObsR_roll p₁ p₂ n :
  n ⊨ MObsR p₁ p₂ → n ⊨ MObsR_fix p₁ p₂.
Proof.
  intro H; iapply (I_fix_roll MObs_sig); [ | exact H ].
  apply F_MObsR_contractive.
Qed.

Lemma MObsR_unroll p₁ p₂ n :
  n ⊨ MObsR_fix p₁ p₂ → n ⊨ MObsR p₁ p₂.
Proof.
  intro H; iapply (I_fix_unroll MObs_sig); [ | exact H ].
  apply F_MObsR_contractive.
Qed.

Lemma MObsR_red_l p₁ p₁' n :
  S.red p₁ p₁' → n ⊨ ∀ᵢ p₂, MObsR p₁' p₂ →ᵢ MObsR p₁ p₂.
Proof.
  intro Hred; loeb_induction.
  iintros p₂ Hp; idestruct Hp as Hp_v Hp_red; idestruct Hp_v.
  isplit.
  + iintro; intros v₂ Heq.
    specialize (Hp_v v₂ Heq); destruct Hp_v as [ v₁ Hred_rtc ].
    exists v₁; econstructor; eassumption.
  + iintros p₂' Hred₂; iapply Hp_red in Hred₂; later_shift.
    apply MObsR_roll; iapply IH; apply MObsR_unroll; assumption.
Qed.

Lemma MObsR_red_r p₁ p₂ p₂' n :
  T.red p₂ p₂' → n ⊨ ▷ MObsR p₁ p₂' → n ⊨ MObsR p₁ p₂.
Proof.
  intros Hred Hp; isplit.
  + iintro; intros v₂ Hv₂; rewrite Hv₂ in Hred.
    exfalso; eapply T.value_do_not_red; eassumption.
  + iintro p; iintro Hred2; idestruct Hred2.
    assert (Heq : p = p₂') by
      (eapply T.red_deterministic; eassumption).
    rewrite Heq; later_shift; apply MObsR_roll; assumption.
Qed.

Lemma MObsR_value (v₁ : S.value ∅) v₂ n :
  n ⊨ MObsR v₁ (T.p_value v₂).
Proof.
  isplit.
  + iintro; intros; eexists; constructor.
  + iintro p; iintro Hred; idestruct Hred.
    exfalso; eapply T.value_do_not_red; eassumption.
Qed.

Lemma MObsR_adequacy (v₂ : T.value _) p₁ p₂ :
  T.red_rtc p₂ (T.p_value v₂) → (∀ n, n ⊨ MObsR p₁ p₂) → S.terminates p₁.
Proof.
  intro RED; remember (T.p_value v₂) as p; revert RED Heqp.
  induction 1; intros Hp Hobs.
  + specialize (Hobs {| nw_index := 0 |}).
    apply I_conj_elim1, I_prop_elim in Hobs.
    eapply Hobs; eassumption.
  + apply IHRED; [ assumption | ].
    intro w; specialize (Hobs (world_lift w)).
    apply MObsR_unroll, I_world_lift_later.
    iapply Hobs; iintro; assumption.
Qed.

(* ========================================================================= *)
(* MObs properties *)

Lemma MObs_red_l p₁ p₁' p₂ n :
  S.red p₁ p₁' → n ⊨ MObs p₁' p₂ → n ⊨ MObs p₁ p₂.
Proof.
  intros Hred Hp; idestruct Hp as HpL HpR.
  isplit.
  + eapply MObsL_red_l; [ eassumption | ].
    iintro; assumption.
  + iapply MObsR_red_l; eassumption.
Qed.

Lemma MObs_red_r p₁ p₂ p₂' n :
  T.red p₂ p₂' → n ⊨ MObs p₁ p₂' → n ⊨ MObs p₁ p₂.
Proof.
  intros Hred Hp; idestruct Hp as HpL HpR.
  isplit.
  + iapply MObsL_red_r; eassumption.
  + eapply MObsR_red_r; [ eassumption | ].
    iintro; assumption.
Qed.

Lemma MObs_red_both p₁ p₁' p₂ p₂' n :
  S.red p₁ p₁' → T.red p₂ p₂' →
  n ⊨ ▷ MObs p₁' p₂' →
  n ⊨ MObs p₁ p₂.
Proof.
  intros Hred1 Hred2 Hp; isplit.
  + iapply MObsL_red_r; [ eassumption | ].
    eapply MObsL_red_l; [ eassumption | ].
    later_shift; idestruct Hp as Hp1 Hp2; assumption.
  + iapply MObsR_red_l; [ eassumption | ].
    eapply MObsR_red_r; [ eassumption | ].
    later_shift; idestruct Hp as Hp1 Hp2; assumption.
Qed.

Lemma MObs_value (v₁ : S.value ∅) v₂ n :
  n ⊨ MObs v₁ (T.p_value v₂).
Proof.
  isplit; [ apply MObsL_value | apply MObsR_value ].
Qed.

Theorem MObs_adequacy p₁ p₂ :
  (∀ n, n ⊨ MObs p₁ p₂) →
    (∃ v₁ : S.value _, S.red_rtc p₁ v₁) ↔ 
    (∃ v₂, T.red_rtc p₂ (T.p_value v₂)).
Proof.
  intro Hobs; split.
  + intros [ v₁ Hv₁ ]; eapply MObsL_adequacy; [ eassumption | ].
    intro; eapply I_conj_elim1; apply Hobs.
  + intros [ v₂ Hv₂ ]; eapply MObsR_adequacy; [ eassumption | ].
    intro; eapply I_conj_elim2; apply Hobs.
Qed.
