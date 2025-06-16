Require Import Utf8.
Require Import Binding.Lib.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common.
Require Import Source.
Require Import LogicalRelation.Core.

Definition F_ObsL (ObsL : Obs_sig) : Obs_sig :=
  λ p₁ p₂,
  (∀ v₁ : value ∅, p₁ = v₁ → terminates p₂)ᵢ ∧ᵢ
  ∀ᵢ p₁' : program ∅, (red p₁ p₁')ᵢ →ᵢ ▷ ObsL p₁' p₂.

Definition ObsL_fix := I_fix F_ObsL.
Definition ObsL := F_ObsL ObsL_fix.

Definition Obs p₁ p₂ := ObsL p₁ p₂ ∧ᵢ ObsL p₂ p₁.

(* ========================================================================= *)

Lemma F_ObsL_contractive : contractive F_ObsL.
Proof.
  intro n; iintros; unfold F_ObsL; auto_contr.
Qed.

Lemma ObsL_roll p₁ p₂ n :
  n ⊨ ObsL p₁ p₂ → n ⊨ ObsL_fix p₁ p₂.
Proof.
  intro H; iapply (I_fix_roll Obs_sig); [ | exact H ].
  apply F_ObsL_contractive.
Qed.

Lemma ObsL_unroll p₁ p₂ n :
  n ⊨ ObsL_fix p₁ p₂ → n ⊨ ObsL p₁ p₂.
Proof.
  intro H; iapply (I_fix_unroll Obs_sig); [ | exact H ].
  apply F_ObsL_contractive.
Qed.

(* ========================================================================= *)
(* ObsL properties *)

Lemma ObsL_red_l p₁ p₁' p₂ n :
  red p₁ p₁' → n ⊨ ▷ ObsL p₁' p₂ → n ⊨ ObsL p₁ p₂.
Proof.
  intros Hred Hp; isplit.
  + iintro; intros v₁ Hv₁; rewrite Hv₁ in Hred.
    exfalso; eapply value_do_not_red; eassumption.
  + iintros p Hred2; idestruct Hred2.
    assert (Heq : p = p₁') by
      (eapply red_deterministic; eassumption).
    rewrite Heq; later_shift; apply ObsL_roll; assumption.
Qed.

Lemma ObsL_red_r p₂ p₂' n :
  red p₂ p₂' → n ⊨ ∀ᵢ p₁, ObsL p₁ p₂' →ᵢ ObsL p₁ p₂.
Proof.
  intro Hred; loeb_induction.
  iintros p₁ Hp; idestruct Hp as Hp_v Hp_red; idestruct Hp_v.
  isplit.
  + iintro; intros v₁ Heq.
    specialize (Hp_v v₁ Heq); destruct Hp_v as [ v₂ Hred_rtc ].
    exists v₂; econstructor; eassumption.
  + iintros p₁' Hred₁; iapply Hp_red in Hred₁; later_shift.
    apply ObsL_roll; iapply IH; apply ObsL_unroll; assumption.
Qed.

Lemma ObsL_value (v₁ v₂ : value ∅) n :
  n ⊨ ObsL v₁ v₂.
Proof.
  isplit.
  + iintro; intros; eexists; constructor.
  + iintro p; iintro Hred; idestruct Hred.
    exfalso; eapply value_do_not_red; eassumption.
Qed.

Lemma ObsL_adequacy (v₁ : value ∅) (p₁ p₂ : program ∅) :
  red_rtc p₁ v₁ → (∀ w, w ⊨ ObsL p₁ p₂) → terminates p₂.
Proof.
  intro RED; remember (p_expr v₁) as p; revert RED Heqp.
  induction 1; intros Hp Hobs.
  + specialize (Hobs {| nw_index := 0 |}).
    apply I_conj_elim1, I_prop_elim in Hobs.
    eapply Hobs; eassumption.
  + apply IHRED; [ assumption | ].
    intro w; specialize (Hobs (world_lift w)).
    apply ObsL_unroll, I_world_lift_later.
    iapply Hobs; iintro; assumption.
Qed.

(* ========================================================================= *)
(* Obs properties *)

Lemma Obs_red_l p₁ p₁' p₂ n :
  red p₁ p₁' → n ⊨ Obs p₁' p₂ → n ⊨ Obs p₁ p₂.
Proof.
  intros Hred Hp; idestruct Hp as Hp1 Hp2.
  isplit.
  + eapply ObsL_red_l; [ eassumption | ].
    iintro; assumption.
  + iapply ObsL_red_r; eassumption.
Qed.

Lemma Obs_red_r p₁ p₂ p₂' n :
  red p₂ p₂' → n ⊨ Obs p₁ p₂' → n ⊨ Obs p₁ p₂.
Proof.
  intros Hred Hp; idestruct Hp as Hp1 Hp2.
  isplit.
  + iapply ObsL_red_r; eassumption.
  + eapply ObsL_red_l; [ eassumption | ].
    iintro; assumption.
Qed.

Lemma Obs_red_both (p₁ p₁' p₂ p₂' : program ∅) n :
  red p₁ p₁' → red p₂ p₂' →
  n ⊨ ▷ Obs p₁' p₂' →
  n ⊨ Obs p₁ p₂.
Proof.
  intros Hred1 Hred2 Hp; isplit.
  + iapply ObsL_red_r; [ eassumption | ].
    eapply ObsL_red_l; [ eassumption | ].
    later_shift; idestruct Hp as Hp1 Hp2; assumption.
  + iapply ObsL_red_r; [ eassumption | ].
    eapply ObsL_red_l; [ eassumption | ].
    later_shift; idestruct Hp as Hp1 Hp2; assumption.
Qed.

Lemma Obs_value (v₁ v₂ : value ∅) n :
  n ⊨ Obs v₁ v₂.
Proof.
  isplit; apply ObsL_value.
Qed.

Theorem Obs_adequacy p₁ p₂ :
  (∀ n, n ⊨ Obs p₁ p₂) → obs_equiv p₁ p₂.
Proof.
  intro Hobs; split.
  + intros [ v₁ Hv₁ ]; eapply ObsL_adequacy; [ eassumption | ].
    intro; iapply Hobs.
  + intros [ v₂ Hv₂ ]; eapply ObsL_adequacy; [ eassumption | ].
    intro; iapply Hobs.
Qed.

#[export]
Instance ObsClass_Equiv : ObsClass :=
  { Obs          := Obs
  ; Obs_red_both := Obs_red_both
  ; Obs_value    := Obs_value
  }.
