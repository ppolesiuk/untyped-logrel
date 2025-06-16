Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common.
Require Import MixedLogicalRelation.MObs.
Require Import MixedLogicalRelation.Core.

Lemma MRelV_intro (v₁ : S.value _) v₂ n :
  n ⊨ (∀ᵢ u₁ u₂, ▷ MRelV u₁ u₂ →ᵢ MRelR (S.e_app v₁ u₁) (T.e_app v₂ u₂)) →
  n ⊨ MRelV v₁ v₂.
Proof.
  intro Hv; iintros u₁ u₂ Hu; iapply Hv.
  later_shift; apply MRelV_unroll; assumption.
Qed.

Lemma MRelK_intro E k n :
  n ⊨ (∀ᵢ v₁ v₂, MRelV v₁ v₂ →ᵢ MObs (S.plug E v₁) (T.p_appK k v₂)) →
  n ⊨ MRelK E k.
Proof.
  intro HEk; iintros v₁ v₂ Hv; iapply HEk; apply MRelV_unroll; assumption.
Qed.

Lemma MRelK_elim E k v₁ v₂ n :
  n ⊨ MRelK E k →
  n ⊨ MRelV v₁ v₂ →
  n ⊨ MObs (S.plug E v₁) (T.p_appK k v₂).
Proof.
  intros HEk Hv; iapply HEk; apply MRelV_roll; assumption.
Qed.

Lemma MRelE_elim e₁ e₂ E k n :
  n ⊨ MRelE e₁ e₂ →
  n ⊨ MRelK E k →
  n ⊨ MObs (S.plug E e₁) (T.p_appE e₂ k).
Proof.
  intros He HE; iapply He; assumption.
Qed.

Lemma MRelV_elimE v₁ v₂ u₁ u₂ n :
  n ⊨ MRelV v₁ v₂ →
  n ⊨ MRelV u₁ u₂ →
  n ⊨ MRelE (S.e_app v₁ u₁) (T.e_app v₂ u₂).
Proof.
  intros Hv Hu; iintros E k HEk.
  iapply Hv; later_shift; [ | assumption ].
  apply MRelV_roll; assumption.
Qed.