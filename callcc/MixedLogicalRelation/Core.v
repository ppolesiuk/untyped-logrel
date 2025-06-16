Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Import IxFree.Lib IxFree.Nat.
Require Import Common.
Require Import MixedLogicalRelation.MObs.

Definition MSemType := S.value ∅ ⇒ᵢ T.value mtC ⇒ᵢ IRel.

Definition F_MRelK (MRelV : MSemType)
    (E : S.ectx ∅) (k : T.cont mtC) :=
  ∀ᵢ v₁ v₂, MRelV v₁ v₂ →ᵢ MObs (S.plug E v₁) (T.p_appK k v₂).

Definition F_MRelR (MRelV : MSemType)
    (e₁ : S.expr ∅) (e₂ : T.expr mtC) :=
  ∀ᵢ E k, ▷ F_MRelK MRelV E k →ᵢ MObs (S.plug E e₁) (T.p_appE e₂ k).

Definition F_MRelV (MRelV : MSemType) : MSemType :=
  λ v₁ v₂,
  ∀ᵢ u₁ u₂, ▷ MRelV u₁ u₂ →ᵢ F_MRelR MRelV (S.e_app v₁ u₁) (T.e_app v₂ u₂).

Definition MRelV_fix := I_fix F_MRelV.

Definition MRelV := F_MRelV MRelV_fix.
Definition MRelR := F_MRelR MRelV_fix.
Definition MRelK := F_MRelK MRelV_fix.

Definition MRelE (e₁ : S.expr ∅) (e₂ : T.expr mtC) : IProp :=
  ∀ᵢ E k, MRelK E k →ᵢ MObs (S.plug E e₁) (T.p_appE e₂ k).

Definition MRelVK (κ : T.kind) : S.value ∅ → T.valuelike κ mtC → IProp :=
  match κ as κ return _ → T.valuelike κ _ → IProp with
  | T.k_val  => MRelV
  | T.k_cont => λ v, MRelK (S.ectx_app2 v S.ectx_hole)
  end.

(* ========================================================================= *)
(* Open relations *)

Definition mrel_G (Δ : T.VCtx)
    (γ₁ : Binding.Set.Sub (dom Δ) ∅) (γ₂ : Sub Δ mtC) : IProp :=
  ∀ᵢ x, MRelVK (Δ x) (γ₁ x) (γ₂ _ x eq_refl).

Definition mrel_e (Δ : T.VCtx)
    (e₁ : S.expr (dom Δ)) (e₂ : T.expr Δ) : IProp :=
  ∀ᵢ γ₁ γ₂, mrel_G Δ γ₁ γ₂ →ᵢ MRelE (bind γ₁ e₁) (bind γ₂ e₂).

Definition mrel_vk {κ : T.kind} (Δ : T.VCtx)
    (v₁ : S.value (dom Δ)) (v₂ : T.valuelike κ Δ) : IProp :=
  ∀ᵢ γ₁ γ₂, mrel_G Δ γ₁ γ₂ →ᵢ MRelVK κ (bind γ₁ v₁) (bind γ₂ v₂).

Definition mrel_p (Δ : T.VCtx)
   (p₁ : S.program (dom Δ)) (p₂ : T.program Δ) : IProp :=
  ∀ᵢ γ₁ γ₂, mrel_G Δ γ₁ γ₂ →ᵢ MObs (bind γ₁ p₁) (bind γ₂ p₂).

(* ========================================================================= *)
(* Contractiveness and urolling fixpoint *)

Lemma F_MRelV_contractive : contractive F_MRelV.
Proof.
  intro n; iintros; unfold F_MRelV, F_MRelR, F_MRelK; auto_contr.
Qed.

Lemma MRelV_roll v₁ v₂ n :
  n ⊨ MRelV v₁ v₂ → n ⊨ MRelV_fix v₁ v₂.
Proof.
  intro H; iapply (I_fix_roll MSemType); [ | exact H ].
  apply F_MRelV_contractive.
Qed.

Lemma MRelV_unroll v₁ v₂ n :
  n ⊨ MRelV_fix v₁ v₂ → n ⊨ MRelV v₁ v₂.
Proof.
  intro H; iapply (I_fix_unroll MSemType); [ | exact H ].
  apply F_MRelV_contractive.
Qed.
