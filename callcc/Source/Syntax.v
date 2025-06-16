Require Import Utf8.
Require Import Binding.Lib Binding.Set.

(** Expressions *)
Inductive expr (V : Set) : Set :=
| e_value  : value V → expr V
| e_app    : expr V → expr V → expr V
| e_callcc : expr (inc V) → expr V
| e_abort  : program V → expr V

(** Values *)
with value (V : Set) : Set :=
| v_var   : V → value V
| v_lam   : expr (inc V) → value V

(** Programs *)
with program (V : Set) : Set :=
| p_expr : expr V → program V
.

Coercion e_value : value >-> expr.
Coercion p_expr  : expr >-> program.

Arguments e_value  {V} v.
Arguments e_app    {V}.
Arguments e_callcc {V}.
Arguments e_abort  {V}.

Arguments v_var   {V} x.
Arguments v_lam   {V} e.

Arguments p_expr {V} e.

(** Inside-out evaluation contexts *)
Inductive ectx (V : Set) :=
| ectx_hole   : ectx V
| ectx_app1   : ectx V → expr V → ectx V
| ectx_app2   : value V → ectx V → ectx V
.

Arguments ectx_hole   {V}.
Arguments ectx_app1   {V} E e.
Arguments ectx_app2   {V} v E.

Fixpoint plug {V : Set} (E : ectx V) (e : expr V) : program V :=
  match E with
  | ectx_hole       => e
  | ectx_app1 E e'  => plug E (e_app e e')
  | ectx_app2 v E   => plug E (e_app v e)
  end.

(** Outside-in evaluation contexts *)
Inductive rctx (V : Set) :=
| rctx_hole   : rctx V
| rctx_app1   : rctx V → expr V → rctx V
| rctx_app2   : value V → rctx V → rctx V
.

Arguments rctx_hole   {V}.
Arguments rctx_app1   {V} E e.
Arguments rctx_app2   {V} v E.

Fixpoint rplug {V : Set} (E : rctx V) (e : expr V) : expr V :=
  match E with
  | rctx_hole       => e
  | rctx_app1 E e'  => e_app (rplug E e) e'
  | rctx_app2 v E   => e_app v (rplug E e)
  end.

(* ========================================================================= *)
(* Pure *)

#[global]
Instance SetPureCore_value : SetPureCore value :=
  { set_pure := @v_var }.

(* ========================================================================= *)
(* Maps *)

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_value v     => e_value (vmap f v)
  | e_app   e₁ e₂ => e_app (emap f e₁) (emap f e₂)
  | e_callcc e    => e_callcc (emap (lift f) e)
  | e_abort  p    => e_abort (pmap f p)
  end

with vmap {A B : Set} (f : A [→] B) (v : value A) : value B :=
  match v with
  | v_var  x     => v_var (f x)
  | v_lam  e     => v_lam (emap (lift f) e)
  end

with pmap {A B : Set} (f : A [→] B) (p : program A) : program B :=
  match p with
  | p_expr e => p_expr (emap f e)
  end.

#[global]
Instance FunctorCore_emap : FunctorCore expr := @emap.
#[global]
Instance FunctorCore_vmap : FunctorCore value := @vmap.
#[global]
Instance FunctorCore_pmap : FunctorCore program := @pmap.

Fixpoint xmap {A B : Set} (f : A [→] B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole       => ectx_hole
  | ectx_app1 E e   => ectx_app1 (xmap f E) (fmap f e)
  | ectx_app2 v E   => ectx_app2 (fmap f v) (xmap f E)
  end.

#[global]
Instance FunctorCore_xmap : FunctorCore ectx := @xmap.

Fixpoint rmap {A B : Set} (f : A [→] B) (E : rctx A) : rctx B :=
  match E with
  | rctx_hole       => rctx_hole
  | rctx_app1 E e   => rctx_app1 (rmap f E) (fmap f e)
  | rctx_app2 v E   => rctx_app2 (fmap f v) (rmap f E)
  end.

#[global]
Instance FunctorCore_rmap : FunctorCore rctx := @rmap.

(* ========================================================================= *)
(* Binds *)

Fixpoint ebind {A B : Set} (f : A [⇒] B) (e : expr A) : expr B :=
  match e with
  | e_value v     => e_value (vbind f v)
  | e_app   e₁ e₂ => e_app (ebind f e₁) (ebind f e₂)
  | e_callcc e    => e_callcc (ebind (lift f) e)
  | e_abort  p    => e_abort (pbind f p)
  end

with vbind {A B : Set} (f : A [⇒] B) (v : value A) : value B :=
  match v with
  | v_var  x     => f x
  | v_lam  e     => v_lam (ebind (lift f) e)
  end

with pbind {A B : Set} (f : A [⇒] B) (p : program A) : program B :=
  match p with
  | p_expr e => p_expr (ebind f e)
  end.

#[global]
Instance BindCore_ebind : BindCore expr := @ebind.
#[global]
Instance BindCore_vbind : BindCore value := @vbind.
#[global]
Instance BindCore_pbind : BindCore program := @pbind.

Fixpoint xbind {A B : Set} (f : A [⇒] B) (E : ectx A) : ectx B :=
  match E with
  | ectx_hole       => ectx_hole
  | ectx_app1 E e   => ectx_app1 (xbind f E) (bind f e)
  | ectx_app2 v E   => ectx_app2 (bind f v) (xbind f E)
  end.

#[global]
Instance BindCore_xbind : BindCore ectx := @xbind.

Fixpoint rbind {A B : Set} (f : A [⇒] B) (E : rctx A) : rctx B :=
  match E with
  | rctx_hole       => rctx_hole
  | rctx_app1 E e   => rctx_app1 (rbind f E) (bind f e)
  | rctx_app2 v E   => rctx_app2 (bind f v) (rbind f E)
  end.

#[global]
Instance BindCore_rbind : BindCore rctx := @rbind.
