Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic Binding.Auto.
Require Import Target.Syntax.

Import Binding.Intrinsic.Notations.

(* ========================================================================= *)
(* Pure properties *)

#[global]
Instance IntPure_valuelike : IntPure valuelike.
Proof. split; reflexivity. Qed.

(* ========================================================================= *)
(* Map properties *)

Lemma vvar_eq {Δ : VCtx} {κ : kind}
    x y (Hxy : x = y) (EQ₁ : Δ x = κ) (EQ₂ : Δ y = κ) :
  v_var x EQ₁ = v_var y EQ₂.
Proof.
  subst; f_equal; apply KindDecEq.UIP.
Qed.

Fixpoint emap_id {A : VCtx} (f : A [→] A) (e : expr A) :
  equal f (arrow_id _) → fmap f e = e
with vmap_id {κ} {A : VCtx} (f : A [→] A) (v : valuelike κ A) :
  equal f (arrow_id _) → fmap f v = v
with pmap_id {A : VCtx} (f : A [→] A) (p : program A) :
  equal f (arrow_id _) → fmap f p = p.
Proof.
  + auto_map_id.
  + auto_map_id.
    apply vvar_eq, EQ.
  + auto_map_id.
Qed.

Fixpoint emap_map_comp {A B C : VCtx}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (e : expr A) :
  equal (arrow_comp f g) h → fmap f (fmap g e) = fmap h e
with vmap_map_comp {κ} {A B C : VCtx}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (v : valuelike κ A) :
  equal (arrow_comp f g) h → fmap f (fmap g v) = fmap h v
with pmap_map_comp {A B C : VCtx}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (p : program A) :
  equal (arrow_comp f g) h → fmap f (fmap g p) = fmap h p.
Proof.
  + auto_map_comp.
  + auto_map_comp.
    apply vvar_eq, EQ.
  + auto_map_comp.
Qed.

#[global]
Instance Functor_expr : Functor expr.
Proof. split; [ exact @emap_id | exact @emap_map_comp ]. Qed.

#[global]
Instance Functor_valuelike {κ} : Functor (valuelike κ).
Proof. split; [ exact (@vmap_id κ) | exact (@vmap_map_comp κ) ]. Qed.

#[global]
Instance Functor_program : Functor program.
Proof. split; [ exact @pmap_id | exact @pmap_map_comp ]. Qed.

(* ========================================================================= *)
(* Bind-Map properties *)

Fixpoint ebind_map_pure {A B : VCtx}
  (f : A [→] B) g (e : expr A) :
  subst_of_arr f ≡ g → fmap f e = bind g e
with vbind_map_pure {κ} {A B : VCtx}
  (f : A [→] B) g (v : valuelike κ A) :
  subst_of_arr f ≡ g → fmap f v = bind g v
with pbind_map_pure {A B : VCtx}
  (f : A [→] B) g (p : program A) :
  subst_of_arr f ≡ g → fmap f p = bind g p.
Proof.
  + auto_map_bind_pure.
  + auto_map_bind_pure.
  + auto_map_bind_pure.
Qed.

#[global]
Instance BindMapPure_expr : BindMapPure expr.
Proof. split; exact @ebind_map_pure. Qed.

#[global]
Instance BindMapPure_valuelike {κ} : BindMapPure (valuelike κ).
Proof. split; exact (@vbind_map_pure κ). Qed.

#[global]
Instance BindMapPure_program : BindMapPure program.
Proof. split; exact @pbind_map_pure. Qed.

Fixpoint ebind_map_comp {A B₁ B₂ C : VCtx}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (e : expr A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e)
with vbind_map_comp {κ} {A B₁ B₂ C : VCtx}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (v : valuelike κ A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ v) = fmap f₁ (bind g₁ v)
with pbind_map_comp {A B₁ B₂ C : VCtx}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (p : program A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ p) = fmap f₁ (bind g₁ p).
Proof.
  + auto_map_bind_comm.
  + auto_map_bind_comm.
  + auto_map_bind_comm.
Qed.

#[global]
Instance BindMapComm_expr : BindMapComm expr.
Proof. split; exact @ebind_map_comp. Qed.

#[global]
Instance BindMapComm_valuelike {κ} : BindMapComm (valuelike κ).
Proof. split; exact (@vbind_map_comp κ). Qed.

#[global]
Instance BindMapComm_program : BindMapComm program.
Proof. split; exact @pbind_map_comp. Qed.

(* ========================================================================= *)
(* Bind properties *)

Fixpoint ebind_pure {A : VCtx} (f : A [⇒] A) (e : expr A) :
  f ≡ arrow_id _ → bind f e = e
with vbind_pure {κ} {A : VCtx} (f : A [⇒] A) (v : valuelike κ A) :
  f ≡ arrow_id _ → bind f v = v
with pbind_pure {A : VCtx} (f : A [⇒] A) (p : program A) :
  f ≡ arrow_id _ → bind f p = p.
Proof.
  + auto_bind_id.
  + auto_bind_id.
  + auto_bind_id.
Qed.

Fixpoint ebind_bind_comp {A B C : VCtx}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (e : expr A) :
  arrow_comp f g ≡ h → bind f (bind g e) = bind h e
with vbind_bind_comp {κ} {A B C : VCtx}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (v : valuelike κ A) :
  arrow_comp f g ≡ h → bind f (bind g v) = bind h v
with pbind_bind_comp {A B C : VCtx}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (p : program A) :
  arrow_comp f g ≡ h → bind f (bind g p) = bind h p.
Proof.
  + auto_bind_comp.
  + auto_bind_comp.
  + auto_bind_comp.
Qed.

#[global]
Instance Bind_expr : Bind expr.
Proof. split; [ exact @ebind_pure | exact @ebind_bind_comp ]. Qed.

#[global]
Instance Bind_valuelike {κ} : Bind (valuelike κ).
Proof. split; [ exact (@vbind_pure κ) | exact (@vbind_bind_comp κ) ]. Qed.

#[global]
Instance Bind_program : Bind program.
Proof. split; [ exact @pbind_pure | exact @pbind_bind_comp ]. Qed.
