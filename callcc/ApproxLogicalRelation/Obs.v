Require Import Utf8.
Require Import Binding.Lib.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common.
Require Import Source.
Require Import LogicalRelation.Core.

(** Step-indexed version of divergence *)
Definition F_Div (Div : program ∅ ⇒ᵢ IRel) : program ∅ ⇒ᵢ IRel :=
  λ p, ∃ᵢ p', (red p p')ᵢ ∧ᵢ ▷ Div p'.

Definition Div_fix := I_fix F_Div.
Notation Div := (F_Div Div_fix).

Definition Obs (p₁ p₂ : program ∅) := Div p₁ ∨ᵢ (terminates p₂)ᵢ.

(* ========================================================================= *)

Lemma F_Div_contractive : contractive F_Div.
Proof.
  intro n; iintros; unfold F_Div; auto_contr.
Qed.

Lemma Div_roll p n :
  n ⊨ Div p → n ⊨ Div_fix p.
Proof.
  intro H; iapply (I_fix_roll (program ∅ ⇒ᵢ IRel)); [ | exact H ].
  apply F_Div_contractive.
Qed.

Lemma Div_unroll p n :
  n ⊨ Div_fix p → n ⊨ Div p.
Proof.
  intro H; iapply (I_fix_unroll (program ∅ ⇒ᵢ IRel)); [ | exact H ].
  apply F_Div_contractive.
Qed.

(* ========================================================================= *)
(* Obs properties *)

Lemma Obs_red_l p₁ p₁' p₂ n :
  red p₁ p₁' → n ⊨ ▷ Obs p₁' p₂ → n ⊨ Obs p₁ p₂.
Proof.
  intros Hred Hp.
  apply I_disj_later_down in Hp.
  idestruct Hp; [ | index_case ].
  + ileft; iexists; isplit; [ iintro; eassumption | ].
    later_shift; apply Div_roll; assumption.
  + ileft; iexists; isplit; [ iintro; eassumption | ].
    later_shift; idestruct HFalse; contradiction.
  + iright; iintro; assumption.
Qed.

Lemma Obs_red_r p₁ p₂ p₂' n :
  red p₂ p₂' → n ⊨ Obs p₁ p₂' → n ⊨ Obs p₁ p₂.
Proof.
  intros Hred Hp.
  idestruct Hp; [ ileft; assumption | iright; idestruct Hp; iintro ].
  destruct Hp as [ v ? ]; exists v; econstructor; eassumption.
Qed.

Lemma Obs_red_both (p₁ p₁' p₂ p₂' : program ∅) n :
  red p₁ p₁' → red p₂ p₂' →
  n ⊨ ▷ Obs p₁' p₂' →
  n ⊨ Obs p₁ p₂.
Proof.
  intros Hred1 Hred2 Hp.
  eapply Obs_red_l; [ eassumption | ]; later_shift.
  eapply Obs_red_r; eassumption.
Qed.

Lemma Obs_value (v₁ v₂ : value ∅) n :
  n ⊨ Obs v₁ v₂.
Proof.
  iright; iintro; eexists; constructor.
Qed.

Theorem Obs_adequacy p₁ p₂ :
  (∀ n, n ⊨ Obs p₁ p₂) → obs_approx p₁ p₂.
Proof.
  intros Hobs [ v₁ RED ].
  remember (p_expr v₁) as pv; induction RED as [ | ? ? ? Hred ].
  + specialize (Hobs {| nw_index := 0 |}); idestruct Hobs as Hobs Hobs.
    - subst; idestruct Hobs as p' Hred ?; idestruct Hred.
      exfalso; eapply value_do_not_red; eassumption.
    - idestruct Hobs; assumption.
  + apply IHRED; [ | assumption ].
    intros n; specialize (Hobs (world_lift n)); idestruct Hobs.
    - ileft; apply Div_unroll, I_world_lift_later.
      idestruct Hobs as p' Hred' Hobs; idestruct Hred'.
      rewrite (red_deterministic _ _ _ Hred Hred'); assumption.
    - idestruct Hobs; iright; iintro; assumption.
Qed.

#[export]
Instance ObsClass_Equiv : ObsClass :=
  { Obs          := Obs
  ; Obs_red_both := Obs_red_both
  ; Obs_value    := Obs_value
  }.
