Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import LogicalRelation.Core.

Section LogicalRelation.
Context {ObsCl : ObsClass}.

Lemma RelV_intro (v₁ v₂ : value ∅) n :
  n ⊨ (∀ᵢ u₁ u₂, ▷ RelV u₁ u₂ →ᵢ RelR (e_app v₁ u₁) (e_app v₂ u₂)) →
  n ⊨ RelV v₁ v₂.
Proof.
  intro Hv; iintros u₁ u₂ Hu; iapply Hv.
  later_shift; apply RelV_unroll; assumption.
Qed.

Lemma RelV_elim (v₁ v₂ u₁ u₂ : value ∅) n :
  n ⊨ RelV v₁ v₂ →
  n ⊨ ▷ RelV u₁ u₂ →
  n ⊨ RelR (e_app v₁ u₁) (e_app v₂ u₂).
Proof.
  intros Hv Hu; iapply Hv.
  later_shift; apply RelV_roll; assumption.
Qed.

Lemma RelK_intro (E₁ E₂ : ectx ∅) n :
  n ⊨ (∀ᵢ v₁ v₂, RelV v₁ v₂ →ᵢ Obs (plug E₁ v₁) (plug E₂ v₂)) →
  n ⊨ RelK E₁ E₂.
Proof.
  intro HE; iintros v₁ v₂ Hv; iapply HE.
  apply RelV_unroll; assumption.
Qed.

Lemma RelK_elim (E₁ E₂ : ectx ∅) (v₁ v₂ : value ∅) n :
  n ⊨ RelK E₁ E₂ →
  n ⊨ RelV v₁ v₂ →
  n ⊨ Obs (plug E₁ v₁) (plug E₂ v₂).
Proof.
  intros HE Hv; iapply HE; apply RelV_roll; assumption.
Qed.

Lemma RelR_elim (e₁ e₂ : expr ∅) E₁ E₂ n :
  n ⊨ RelR e₁ e₂ →
  n ⊨ ▷ RelK E₁ E₂ →
  n ⊨ Obs (plug E₁ e₁) (plug E₂ e₂).
Proof.
  intros He HE; iapply He; assumption.
Qed.

Lemma RelE_elim (e₁ e₂ : expr ∅) E₁ E₂ n :
  n ⊨ RelE e₁ e₂ →
  n ⊨ RelK E₁ E₂ →
  n ⊨ Obs (plug E₁ e₁) (plug E₂ e₂).
Proof.
  intros He HE; iapply He; assumption.
Qed.

Lemma RelV_elimE (v₁ v₂ u₁ u₂ : value ∅) n :
  n ⊨ RelV v₁ v₂ →
  n ⊨ RelV u₁ u₂ →
  n ⊨ RelE (e_app v₁ u₁) (e_app v₂ u₂).
Proof.
  intros Hv Hu; iintros E₁ E₂ HE.
  apply RelR_elim; [ | later_shift; assumption ].
  apply RelV_elim; [ assumption | ].
  later_shift; assumption.
Qed.

End LogicalRelation.
