Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Auto.
Require Import Source.Syntax.

Lemma fmap_plug {A B : Set} (f : A [→] B) (E : ectx A) e :
  fmap f (plug E e) = plug (fmap f E) (fmap f e).
Proof.
  revert e; induction E; intros; term_simpl; try reflexivity; apply IHE.
Qed.

Lemma bind_plug {A B : Set} (f : A [⇒] B) (E : ectx A) e :
  bind f (plug E e) = plug (bind f E) (bind f e).
Proof.
  revert e; induction E; intros; term_simpl; try reflexivity; apply IHE.
Qed.

Lemma subst_plug {V : Set} (E : ectx (inc V)) e v :
  subst (plug E e) v = plug (subst E v) (subst e v).
Proof. apply bind_plug. Qed.

#[global] Hint Rewrite @fmap_plug  : term_simpl.
#[global] Hint Rewrite @bind_plug  : term_simpl.
#[global] Hint Rewrite @subst_plug : term_simpl.

Lemma fmap_rplug {A B : Set} (f : A [→] B) (E : rctx A) e :
  fmap f (rplug E e) = rplug (fmap f E) (fmap f e).
Proof.
  revert e; induction E; intros; term_simpl; try reflexivity;
    f_equal; apply IHE.
Qed.

Lemma bind_rplug {A B : Set} (f : A [⇒] B) (E : rctx A) e :
  bind f (rplug E e) = rplug (bind f E) (bind f e).
Proof.
  revert e; induction E; intros; term_simpl; try reflexivity;
    f_equal; apply IHE.
Qed.

Lemma subst_rplug {V : Set} (E : rctx (inc V)) e v :
  subst (rplug E e) v = rplug (subst E v) (subst e v).
Proof. apply bind_rplug. Qed.

#[global] Hint Rewrite @fmap_rplug  : term_simpl.
#[global] Hint Rewrite @bind_rplug  : term_simpl.
#[global] Hint Rewrite @subst_rplug : term_simpl.

(* ========================================================================= *)
(* Pure properties *)

#[global]
Instance SetPure_value : SetPure value.
Proof. split; reflexivity. Qed.

(* ========================================================================= *)
(* Map properties *)

Fixpoint emap_id {A : Set} (f : A [→] A) (e : expr A) :
  equal f (arrow_id _) → fmap f e = e
with vmap_id {A : Set} (f : A [→] A) (v : value A) :
  equal f (arrow_id _) → fmap f v = v
with pmap_id {A : Set} (f : A [→] A) (p : program A) :
  equal f (arrow_id _) → fmap f p = p.
Proof.
  + auto_map_id.
  + auto_map_id.
  + auto_map_id.
Qed.

Fixpoint emap_map_comp {A B C : Set}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (e : expr A) :
  equal (arrow_comp f g) h → fmap f (fmap g e) = fmap h e
with vmap_map_comp {A B C : Set}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (v : value A) :
  equal (arrow_comp f g) h → fmap f (fmap g v) = fmap h v
with pmap_map_comp {A B C : Set}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (p : program A) :
  equal (arrow_comp f g) h → fmap f (fmap g p) = fmap h p.
Proof.
  + auto_map_comp.
  + auto_map_comp.
  + auto_map_comp.
Qed.

#[global]
Instance Functor_expr : Functor expr.
Proof. split; [ exact @emap_id | exact @emap_map_comp ]. Qed.

#[global]
Instance Functor_value : Functor value.
Proof. split; [ exact @vmap_id | exact @vmap_map_comp ]. Qed.

#[global]
Instance Functor_program : Functor program.
Proof. split; [ exact @pmap_id | exact @pmap_map_comp ]. Qed.

Fixpoint xmap_id {A : Set} (f : A [→] A) (E : ectx A) :
  equal f (arrow_id _) → fmap f E = E.
Proof. auto_map_id. Qed.

Fixpoint xmap_map_comp {A B C : Set}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (E : ectx A) :
  equal (arrow_comp f g) h → fmap f (fmap g E) = fmap h E.
Proof. auto_map_comp. Qed.

#[global]
Instance Functor_ectx : Functor ectx.
Proof. split; [ exact @xmap_id | exact @xmap_map_comp ]. Qed.

Fixpoint rmap_id {A : Set} (f : A [→] A) (E : rctx A) :
  equal f (arrow_id _) → fmap f E = E.
Proof. auto_map_id. Qed.

Fixpoint rmap_map_comp {A B C : Set}
  (f : B [→] C) (g : A [→] B) (h : A [→] C) (E : rctx A) :
  equal (arrow_comp f g) h → fmap f (fmap g E) = fmap h E.
Proof. auto_map_comp. Qed.

#[global]
Instance Functor_rctx : Functor rctx.
Proof. split; [ exact @rmap_id | exact @rmap_map_comp ]. Qed.

(* ========================================================================= *)
(* Bind-Map properties *)

Fixpoint ebind_map_pure {A B : Set}
  (f : A [→] B) g (e : expr A) :
  subst_of_arr f ≡ g → fmap f e = bind g e
with vbind_map_pure {A B : Set}
  (f : A [→] B) g (v : value A) :
  subst_of_arr f ≡ g → fmap f v = bind g v
with pbind_map_pure {A B : Set}
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
Instance BindMapPure_value : BindMapPure value.
Proof. split; exact @vbind_map_pure. Qed.

#[global]
Instance BindMapPure_program : BindMapPure program.
Proof. split; exact @pbind_map_pure. Qed.

Fixpoint xbind_map_pure {A B : Set}
  (f : A [→] B) g (E : ectx A) :
  subst_of_arr f ≡ g → fmap f E = bind g E.
Proof. auto_map_bind_pure. Qed.

#[global]
Instance BindMapPure_ectx : BindMapPure ectx.
Proof. split; exact @xbind_map_pure. Qed.

Fixpoint rbind_map_pure {A B : Set}
  (f : A [→] B) g (E : rctx A) :
  subst_of_arr f ≡ g → fmap f E = bind g E.
Proof. auto_map_bind_pure. Qed.

#[global]
Instance BindMapPure_rctx : BindMapPure rctx.
Proof. split; exact @rbind_map_pure. Qed.

Fixpoint ebind_map_comp {A B₁ B₂ C : Set}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (e : expr A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e)
with vbind_map_comp {A B₁ B₂ C : Set}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (v : value A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ v) = fmap f₁ (bind g₁ v)
with pbind_map_comp {A B₁ B₂ C : Set}
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
Instance BindMapComm_value : BindMapComm value.
Proof. split; exact @vbind_map_comp. Qed.

#[global]
Instance BindMapComm_program : BindMapComm program.
Proof. split; exact @pbind_map_comp. Qed.

Fixpoint xbind_map_comp {A B₁ B₂ C : Set}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (E : ectx A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ E) = fmap f₁ (bind g₁ E).
Proof. auto_map_bind_comm. Qed.

#[global]
Instance BindMapComm_ectx : BindMapComm ectx.
Proof. split; exact @xbind_map_comp. Qed.

Fixpoint rbind_map_comp {A B₁ B₂ C : Set}
  (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C)
  (E : rctx A) :
    arrow_comp g₂ (subst_of_arr f₂) ≡ arrow_comp (subst_of_arr f₁) g₁ →
      bind g₂ (fmap f₂ E) = fmap f₁ (bind g₁ E).
Proof. auto_map_bind_comm. Qed.

#[global]
Instance BindMapComm_rctx : BindMapComm rctx.
Proof. split; exact @rbind_map_comp. Qed.

(* ========================================================================= *)
(* Bind properties *)

Fixpoint ebind_pure {A : Set} (f : A [⇒] A) (e : expr A) :
  f ≡ arrow_id _ → bind f e = e
with vbind_pure {A : Set} (f : A [⇒] A) (v : value A) :
  f ≡ arrow_id _ → bind f v = v
with pbind_pure {A : Set} (f : A [⇒] A) (p : program A) :
  f ≡ arrow_id _ → bind f p = p.
Proof.
  + auto_bind_id.
  + auto_bind_id.
  + auto_bind_id.
Qed.

Fixpoint ebind_bind_comp {A B C : Set}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (e : expr A) :
  arrow_comp f g ≡ h → bind f (bind g e) = bind h e
with vbind_bind_comp {A B C : Set}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (v : value A) :
  arrow_comp f g ≡ h → bind f (bind g v) = bind h v
with pbind_bind_comp {A B C : Set}
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
Instance Bind_value : Bind value.
Proof. split; [ exact @vbind_pure | exact @vbind_bind_comp ]. Qed.

#[global]
Instance Bind_program : Bind program.
Proof. split; [ exact @pbind_pure | exact @pbind_bind_comp ]. Qed.

Fixpoint xbind_pure {A : Set} (f : A [⇒] A) (E : ectx A) :
  f ≡ arrow_id _ → bind f E = E.
Proof. auto_bind_id. Qed.

Fixpoint xbind_bind_comp {A B C : Set}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (E : ectx A) :
  arrow_comp f g ≡ h → bind f (bind g E) = bind h E.
Proof. auto_bind_comp. Qed.

#[global]
Instance Bind_ectx : Bind ectx.
Proof. split; [ exact @xbind_pure | exact @xbind_bind_comp ]. Qed.

Fixpoint rbind_pure {A : Set} (f : A [⇒] A) (E : rctx A) :
  f ≡ arrow_id _ → bind f E = E.
Proof. auto_bind_id. Qed.

Fixpoint rbind_bind_comp {A B C : Set}
  (f : B [⇒] C) (g : A [⇒] B) (h : A [⇒] C) (E : rctx A) :
  arrow_comp f g ≡ h → bind f (bind g E) = bind h E.
Proof. auto_bind_comp. Qed.

#[global]
Instance Bind_rctx : Bind rctx.
Proof. split; [ exact @rbind_pure | exact @rbind_bind_comp ]. Qed.
