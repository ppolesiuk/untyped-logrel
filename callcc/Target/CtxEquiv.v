Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import Target.Syntax.
Require Import Target.Reduction.
Require Import RelationClasses.

Import Binding.Intrinsic.Notations.

(** Inside-out general contexts (for expressions) *)
Inductive ctxE : VCtx → Type :=
| ctx_fmap  : ∀ A B, (Arr A B) → ctxE B → ctxE A
| ctx_bind  : ∀ A B, (A [⇒] B) → ctxE B → ctxE A
| ctx_vlam  : ∀ Δ, ctxV Δ → ctxE (extC k_val Δ)
| ctx_appE1 : ∀ Δ, ctxP Δ → cont Δ → ctxE Δ

(** Inside-out general contexts (for values) *)
with ctxV : VCtx → Type :=
| ctx_fmapv : ∀ A B, (Arr A B) → ctxV B → ctxV A
| ctx_app1  : ∀ Δ, ctxE Δ → value Δ → ctxV Δ
| ctx_app2  : ∀ Δ, value Δ → ctxE Δ → ctxV Δ
| ctx_value : ∀ Δ, ctxP Δ → ctxV Δ
| ctx_appK2 : ∀ Δ, cont Δ → ctxP Δ → ctxV Δ

(** Inside-out general contexts (for continuations) *)
with ctxK : VCtx → Type :=
| ctx_appE2 : ∀ Δ, expr Δ → ctxP Δ → ctxK Δ
| ctx_appK1 : ∀ Δ, ctxP Δ → value Δ → ctxK Δ

(** Inside-out general contexts (for programs) *)
with ctxP  : VCtx → Type :=
| ctx_hole : ctxP mtC
| ctx_elam : ∀ Δ, ctxE Δ → ctxP (extC k_cont Δ)
| ctx_clam : ∀ Δ, ctxK Δ → ctxP (extC k_val Δ)
.

Arguments ctx_fmap  {A} {B} f C.
Arguments ctx_bind  {A} {B} f C.
Arguments ctx_vlam  {Δ} C.
Arguments ctx_appE1 {Δ} C k.
Arguments ctx_fmapv {A} {B} f C.
Arguments ctx_app1  {Δ} C v.
Arguments ctx_app2  {Δ} v C.
Arguments ctx_value {Δ} C.
Arguments ctx_appK2 {Δ} k C.
Arguments ctx_appE2 {Δ} e C.
Arguments ctx_appK1 {Δ} C v.
Arguments ctx_elam  {Δ} C.
Arguments ctx_clam  {Δ} C.

Fixpoint plugE {Δ} (C : ctxE Δ) : expr Δ → program mtC :=
  match C with
  | ctx_fmap  f C => λ e, plugE C (fmap f e)
  | ctx_bind  f C => λ e, plugE C (bind f e)
  | ctx_vlam  C   => λ e, plugV C (v_vlam e)
  | ctx_appE1 C k => λ e, plugP C (p_appE e k)
  end

with plugV {Δ} (C : ctxV Δ) : value Δ → program mtC :=
  match C with
  | ctx_fmapv f C => λ v, plugV C (fmap f v)
  | ctx_app1  C u => λ v, plugE C (e_app v u)
  | ctx_app2  u C => λ v, plugE C (e_app u v)
  | ctx_value C   => λ v, plugP C (p_value v)
  | ctx_appK2 k C => λ v, plugP C (p_appK k v)
  end

with plugK {Δ} (C : ctxK Δ) : cont Δ → program mtC :=
  match C with
  | ctx_appE2 e C => λ k, plugP C (p_appE e k)
  | ctx_appK1 C v => λ k, plugP C (p_appK k v)
  end

with plugP {Δ} (C : ctxP Δ) : program Δ → program mtC :=
  match C with
  | ctx_hole   => λ p, p
  | ctx_elam C => λ p, plugE C (e_lam p)
  | ctx_clam C => λ p, plugK C (v_clam p)
  end.

(** Observational equivalence of complete programs *)
Definition obs_equiv (p₁ p₂ : program mtC) : Prop :=
  terminates p₁ ↔ terminates p₂.

#[global]
Instance Reflexive_obs_equiv : Reflexive obs_equiv.
Proof.
  intro p; unfold obs_equiv; tauto.
Qed.

#[global]
Instance Symmetric_obs_equiv : Symmetric obs_equiv.
Proof.
  intros p₁ p₂; unfold obs_equiv; tauto.
Qed.

#[global]
Instance Transitive_obs_equiv : Transitive obs_equiv.
Proof.
  intros p₁ p₂ p₃; unfold obs_equiv; tauto.
Qed.

(** Contextual equivalence *)
Definition ctx_equiv {Δ : VCtx} (e₁ e₂ : expr Δ) : Prop :=
  ∀ C, obs_equiv (plugE C e₁) (plugE C e₂).

#[global]
Instance Reflexive_ctx_equiv {Δ} : Reflexive (@ctx_equiv Δ).
Proof.
  intros e C; reflexivity.
Qed.

#[global]
Instance Symmetric_ctx_equiv {Δ} : Symmetric (@ctx_equiv Δ).
Proof.
  intros e₁ e₂ H C; symmetry; apply H.
Qed.

#[global]
Instance Transitive_ctx_equiv {Δ} : Transitive (@ctx_equiv Δ).
Proof.
  intros e₁ e₂ e₃ H1 H2 C; etransitivity; [ apply H1 | apply H2 ].
Qed.
