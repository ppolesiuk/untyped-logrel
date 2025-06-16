Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source Common.

Definition Obs_sig := program ∅ ⇒ᵢ program ∅ ⇒ᵢ IRel.

Class ObsClass : Type :=
  { Obs : Obs_sig
  ; Obs_red_both (p₁ p₁' p₂ p₂' : program ∅) n :
      red p₁ p₁' → red p₂ p₂' →
      n ⊨ ▷ Obs p₁' p₂' →
      n ⊨ Obs p₁ p₂
  ; Obs_value (v₁ v₂ : value ∅) n : n ⊨ Obs v₁ v₂
  }.

Section LogicalRelation.

Context {ObsCl : ObsClass}.

Definition SemType := value ∅ ⇒ᵢ value ∅ ⇒ᵢ IRel.

Definition F_RelK (RelV : SemType) (E₁ E₂ : ectx ∅) :=
  ∀ᵢ v₁ v₂ : value ∅, RelV v₁ v₂ →ᵢ Obs (plug E₁ v₁) (plug E₂ v₂).

Definition F_RelR (RelV : SemType) (e₁ e₂ : expr ∅) :=
  ∀ᵢ E₁ E₂, ▷ F_RelK RelV E₁ E₂ →ᵢ Obs (plug E₁ e₁) (plug E₂ e₂).

Definition F_RelV (RelV : SemType) : SemType :=
  λ v₁ v₂,
  ∀ᵢ u₁ u₂, ▷ RelV u₁ u₂ →ᵢ F_RelR RelV (e_app v₁ u₁) (e_app v₂ u₂).

Definition RelV_fix := I_fix F_RelV.

Definition RelV := F_RelV RelV_fix.
Definition RelR := F_RelR RelV_fix.
Definition RelK := F_RelK RelV_fix.

Definition RelE (e₁ e₂ : expr ∅) : IProp :=
  ∀ᵢ E₁ E₂ : ectx _, RelK E₁ E₂ →ᵢ Obs (plug E₁ e₁) (plug E₂ e₂).

(* ========================================================================= *)
(* Open relations *)

Definition rel_G {V : Set} (γ₁ γ₂ : V [⇒] ∅) : IProp :=
  ∀ᵢ x, RelV (γ₁ x) (γ₂ x).

Definition rel_e {V : Set} (e₁ e₂ : expr V) : IProp :=
  ∀ᵢ γ₁ γ₂, rel_G γ₁ γ₂ →ᵢ RelE (bind γ₁ e₁) (bind γ₂ e₂).

Definition rel_v {V : Set} (v₁ v₂ : value V) : IProp :=
  ∀ᵢ γ₁ γ₂, rel_G γ₁ γ₂ →ᵢ RelV (bind γ₁ v₁) (bind γ₂ v₂).

Definition rel_p {V : Set} (p₁ p₂ : program V) : IProp :=
  ∀ᵢ γ₁ γ₂, rel_G γ₁ γ₂ →ᵢ Obs (bind γ₁ p₁) (bind γ₂ p₂).

(* ========================================================================= *)
(* Contractiveness and urolling fixpoint *)

Lemma F_RelV_contractive : contractive F_RelV.
Proof.
  intro n; iintros; unfold F_RelV, F_RelR, F_RelK; auto_contr.
Qed.

Lemma RelV_roll v₁ v₂ n :
  n ⊨ RelV v₁ v₂ → n ⊨ RelV_fix v₁ v₂.
Proof.
  intro H; iapply (I_fix_roll SemType); [ | exact H ].
  apply F_RelV_contractive.
Qed.

Lemma RelV_unroll v₁ v₂ n :
  n ⊨ RelV_fix v₁ v₂ → n ⊨ RelV v₁ v₂.
Proof.
  intro H; iapply (I_fix_unroll SemType); [ | exact H ].
  apply F_RelV_contractive.
Qed.

End LogicalRelation.
