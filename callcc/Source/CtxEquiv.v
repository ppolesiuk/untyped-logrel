Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import Source.Syntax.
Require Import Source.Reduction.
Require Import RelationClasses.

(** Inside-out general contexts. *)
Inductive ctx : Set → Type :=
| ctx_hole   : ctx ∅
| ctx_fmap   : ∀ A B, (Arr A B) → ctx B → ctx A
| ctx_bind   : ∀ A B, (Sub (F:=value) A B) → ctx B → ctx A
| ctx_lam    : ∀ V, ctx V → ctx (inc V)
| ctx_app1   : ∀ V, ctx V → expr V → ctx V
| ctx_app2   : ∀ V, expr V → ctx V → ctx V
| ctx_callcc : ∀ V, ctx V → ctx (inc V)
| ctx_abort  : ∀ V, ctx V → ctx V
.

Arguments ctx_fmap   {A} {B} f C.
Arguments ctx_bind   {A} {B} f C.
Arguments ctx_lam    {V} C.
Arguments ctx_app1   {V} C e₂.
Arguments ctx_app2   {V} e₁ C.
Arguments ctx_callcc {V} C.
Arguments ctx_abort  {V} C.

Fixpoint cplug {V : Set} (C : ctx V) : expr V → program ∅ :=
  match C with
  | ctx_hole      => p_expr
  | ctx_fmap f C  => λ e, cplug C (fmap f e)
  | ctx_bind f C  => λ e, cplug C (bind f e)
  | ctx_lam  C    => λ e, cplug C (v_lam e)
  | ctx_app1 C e₂ => λ e, cplug C (e_app e e₂)
  | ctx_app2 e₁ C => λ e, cplug C (e_app e₁ e)
  | ctx_callcc  C => λ e, cplug C (e_callcc e)
  | ctx_abort   C => λ e, cplug C (e_abort e)
  end.

(** Observational approximation for complete programs *)
Definition obs_approx (p₁ p₂ : program ∅) : Prop :=
  terminates p₁ → terminates p₂.

(** Observational equivalence for complete programs *)
Definition obs_equiv (p₁ p₂ : program ∅) : Prop :=
  terminates p₁ ↔ terminates p₂.

#[global]
Instance Reflexive_obs_approx : Reflexive obs_approx.
Proof. firstorder. Qed.

#[global]
Instance Transitive_obs_approx : Transitive obs_approx.
Proof. firstorder. Qed.

#[global]
Instance Reflexive_obs_equiv : Reflexive obs_equiv.
Proof. firstorder. Qed.

#[global]
Instance Symmetric_obs_equiv : Symmetric obs_equiv.
Proof. firstorder. Qed.

#[global]
Instance Transitive_obs_equiv : Transitive obs_equiv.
Proof. firstorder. Qed.

(** Contextual approximation *)
Definition ctx_approx {V : Set} (e₁ e₂ : expr V) : Prop :=
  ∀ C, obs_approx (cplug C e₁) (cplug C e₂).

(** Contextual equivalence *)
Definition ctx_equiv {V : Set} (e₁ e₂ : expr V) : Prop :=
  ∀ C, obs_equiv (cplug C e₁) (cplug C e₂).

#[global]
Instance Reflexive_ctx_approx {V : Set} : Reflexive (@ctx_approx V).
Proof.
  intros e C; reflexivity.
Qed.

#[global]
Instance Transitive_ctx_approx {V : Set} : Transitive (@ctx_approx V).
Proof.
  intros e₁ e₂ e₃ H1 H2 C; etransitivity; [ apply H1 | apply H2 ].
Qed.

#[global]
Instance Reflexive_ctx_equiv {V : Set} : Reflexive (@ctx_equiv V).
Proof.
  intros e C; reflexivity.
Qed.

#[global]
Instance Symmetric_ctx_equiv {V : Set} : Symmetric (@ctx_equiv V).
Proof.
  intros e₁ e₂ H C; symmetry; apply H.
Qed.

#[global]
Instance Transitive_ctx_equiv {V : Set} : Transitive (@ctx_equiv V).
Proof.
  intros e₁ e₂ e₃ H1 H2 C; etransitivity; [ apply H1 | apply H2 ].
Qed.

Lemma ctx_equiv_both_approx {V : Set} (e₁ e₂ : expr V) :
  ctx_approx e₁ e₂ → ctx_approx e₂ e₁ → ctx_equiv e₁ e₂.
Proof.
  intros H1 H2 C; split; apply H1 || apply H2.
Qed.
