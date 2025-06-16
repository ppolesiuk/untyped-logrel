Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import Eqdep_dec.

Import Binding.Intrinsic.Notations.

(** Kinds of variables *)
Inductive kind :=
| k_val  : kind
| k_cont : kind
.

Module KindDec <: DecidableType.
  Definition U := kind.

  Lemma eq_dec : ∀ κ₁ κ₂ : U, {κ₁ = κ₂} + {κ₁ ≠ κ₂}.
  Proof. decide equality. Qed.
End KindDec.

Module KindDecEq := DecidableEqDep(KindDec).

Notation VCtx := (Ctx kind).

(** Expressions (computations) *)
Inductive expr (Δ : VCtx) : Set :=
| e_lam : program (extC k_cont Δ) → expr Δ
| e_app : val Δ k_val → val Δ k_val → expr Δ

(** Value-like terms *)
with val (Δ : VCtx) : kind → Set :=
| v_var  : ∀ {κ : kind} (x : dom Δ), Δ x = κ → val Δ κ
| v_vlam : expr (extC k_val Δ) → val Δ k_val
| v_clam : program (extC k_val Δ) → val Δ k_cont

(** Programs *)
with program (Δ : VCtx) : Set :=
| p_value : val Δ k_val → program Δ
| p_appE  : expr Δ → val Δ k_cont → program Δ
| p_appK  : val Δ k_cont → val Δ k_val → program Δ
.

Arguments e_lam {Δ} p.
Arguments e_app {Δ} v u.

Arguments v_var {Δ} {κ} x EQ.
Arguments v_vlam {Δ} e.
Arguments v_clam {Δ} e.

Arguments p_value {Δ} v.
Arguments p_appE  {Δ} e k.
Arguments p_appK  {Δ} k v.

Definition valuelike κ Δ := val Δ κ.

Notation value := (valuelike k_val).
Notation cont  := (valuelike k_cont).

(* ========================================================================= *)
(* Pure *)

#[global]
Instance IntPureCore_typelike : IntPureCore valuelike := @v_var.

(* ========================================================================= *)
(* Maps *)

Fixpoint emap {Δ₁ Δ₂ : VCtx} (f : Δ₁ [→] Δ₂) (e : expr Δ₁) : expr Δ₂ :=
  match e with
  | e_lam p   => e_lam (pmap (lift f) p)
  | e_app v u => e_app (vmap f v) (vmap f u)
  end

with vmap {κ : kind} {Δ₁ Δ₂ : VCtx}
    (f : Δ₁ [→] Δ₂) (v : valuelike κ Δ₁) : valuelike κ Δ₂ :=
  match v with
  | v_var x EQ => v_var (f x) (eq_trans (arr_hom f x) EQ)
  | v_vlam e   => v_vlam (emap (lift f) e)
  | v_clam p   => v_clam (pmap (lift f) p)
  end

with pmap {Δ₁ Δ₂ : VCtx} (f : Δ₁ [→] Δ₂) (p : program Δ₁) : program Δ₂ :=
  match p with
  | p_value  v => p_value (vmap f v)
  | p_appE e k => p_appE (emap f e) (vmap f k)
  | p_appK k v => p_appK (vmap f k) (vmap f v)
  end.

#[global]
Instance FunctorCore_emap : FunctorCore expr := @emap.
#[global]
Instance FunctorCore_vmap {κ} : FunctorCore (valuelike κ) := @vmap κ.
#[global]
Instance FunctorCore_pmap : FunctorCore program := @pmap.

(* ========================================================================= *)
(* Binds *)

Fixpoint ebind {Δ₁ Δ₂ : VCtx} (f : Δ₁ [⇒] Δ₂) (e : expr Δ₁) : expr Δ₂ :=
  match e with
  | e_lam p   => e_lam (pbind (lift f) p)
  | e_app v u => e_app (vbind f v) (vbind f u)
  end

with vbind {κ : kind} {Δ₁ Δ₂ : VCtx}
    (f : Δ₁ [⇒] Δ₂) (v : valuelike κ Δ₁) : valuelike κ Δ₂ :=
  match v with
  | v_var x EQ => f _ x EQ
  | v_vlam e   => v_vlam (ebind (lift f) e)
  | v_clam p   => v_clam (pbind (lift f) p)
  end

with pbind {Δ₁ Δ₂ : VCtx} (f : Δ₁ [⇒] Δ₂) (p : program Δ₁) : program Δ₂ :=
  match p with
  | p_value  v => p_value (vbind f v)
  | p_appE e k => p_appE (ebind f e) (vbind f k)
  | p_appK k v => p_appK (vbind f k) (vbind f v)
  end.

#[global]
Instance BindCore_ebind : BindCore expr := @ebind.
#[global]
Instance BindCore_vbind {κ} : BindCore (valuelike κ) := @vbind κ.
#[global]
Instance BindCore_pbind : BindCore program := @pbind.
