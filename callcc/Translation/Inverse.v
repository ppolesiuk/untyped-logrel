Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Import Common.

Fixpoint expr_uncps {Δ : T.VCtx} (e : T.expr Δ) : S.expr (dom Δ) :=
  match e with
  | T.e_lam p     => S.e_callcc (S.e_abort (program_uncps p))
  | T.e_app v₁ v₂ => S.e_app (value_uncps v₁) (value_uncps v₂)
  end

with value_uncps {κ : T.kind} {Δ : T.VCtx} (v : T.valuelike κ Δ) :
    S.value (dom Δ):=
  match v with
  | T.v_var x _ => S.v_var x
  | T.v_vlam e  => S.v_lam (expr_uncps e)
  | T.v_clam p  => S.v_lam (program_uncps p)
  end

with program_uncps {Δ : T.VCtx} (p : T.program Δ) : S.expr (dom Δ) :=
  match p with
  | T.p_value  v => value_uncps v
  | T.p_appE e k => S.e_app (value_uncps k) (expr_uncps e)
  | T.p_appK k v => S.e_app (value_uncps k) (value_uncps v)
  end.

Definition sub_uncps {Δ₁ Δ₂ : T.VCtx} (f : Binding.Intrinsic.Sub Δ₁ Δ₂) :
    Binding.Set.Sub (dom Δ₁) (dom Δ₂) :=
  {| Binding.Set.apply_sub x := value_uncps (f (Δ₁ x) x eq_refl)
  |}.

Fixpoint ctxE_uncps {Δ : T.VCtx} (C : T.ctxE Δ) : S.ctx (dom Δ) :=
  match C with
  | T.ctx_fmap f C  => S.ctx_fmap (Forget.forget f) (ctxE_uncps C)
  | T.ctx_bind f C  => S.ctx_bind (sub_uncps f) (ctxE_uncps C)
  | T.ctx_vlam C    => S.ctx_lam (ctxV_uncps C)
  | T.ctx_appE1 C k => S.ctx_app2 (value_uncps k) (ctxP_uncps C)
  end

with ctxV_uncps {Δ : T.VCtx} (C : T.ctxV Δ) : S.ctx (dom Δ) :=
  match C with
  | T.ctx_fmapv f C => S.ctx_fmap (Forget.forget f) (ctxV_uncps C)
  | T.ctx_app1 C v  => S.ctx_app1 (ctxE_uncps C) (value_uncps v)
  | T.ctx_app2 v C  => S.ctx_app2 (value_uncps v) (ctxE_uncps C)
  | T.ctx_value C   => ctxP_uncps C
  | T.ctx_appK2 k C => S.ctx_app2 (value_uncps k) (ctxP_uncps C)
  end

with ctxK_uncps {Δ : T.VCtx} (C : T.ctxK Δ) : S.ctx (dom Δ) :=
  match C with
  | T.ctx_appE2 e C => S.ctx_app1 (ctxP_uncps C) (expr_uncps e)
  | T.ctx_appK1 C v => S.ctx_app1 (ctxP_uncps C) (value_uncps v)
  end

with ctxP_uncps {Δ : T.VCtx} (C : T.ctxP Δ) : S.ctx (dom Δ) :=
  match C in T.ctxP Δ return S.ctx (dom Δ) with
  | T.ctx_hole   => S.ctx_hole
  | T.ctx_elam C => S.ctx_abort (S.ctx_callcc (ctxE_uncps C))
  | T.ctx_clam C => S.ctx_lam (ctxK_uncps C)
  end.

(* ========================================================================= *)

Fixpoint expr_uncps_fmap {A B : T.VCtx}
    (f : Binding.Set.Arr (dom A) (dom B)) (g : Arr A B) (e : T.expr A) :
  (∀ x, f x = g x) →
  fmap f (expr_uncps e) = expr_uncps (fmap g e)
with value_uncps_fmap {κ} {A B : T.VCtx}
    (f : Binding.Set.Arr (dom A) (dom B)) (g : Arr A B) (v : T.valuelike κ A) :
  (∀ x, f x = g x) →
  fmap f (value_uncps v) = value_uncps (fmap g v)
with program_uncps_fmap {A B : T.VCtx}
    (f : Binding.Set.Arr (dom A) (dom B)) (g : Arr A B) (p : T.program A) :
  (∀ x, f x = g x) →
  fmap f (program_uncps p) = program_uncps (fmap g p).
Proof.
{ intro Heq; destruct e; term_simpl; repeat f_equal.
  + erewrite <- program_uncps_fmap; [ reflexivity | ].
    intros [ | x ]; term_simpl; f_equal; apply Heq.
  + apply value_uncps_fmap; assumption.
  + apply value_uncps_fmap; assumption.
}
{ intro Heq; destruct v; term_simpl; repeat f_equal.
  + apply Heq.
  + erewrite <- expr_uncps_fmap; [ reflexivity | ].
    intros [ | x ]; term_simpl; f_equal; apply Heq.
  + erewrite <- program_uncps_fmap; [ reflexivity | ].
    intros [ | x ]; term_simpl; f_equal; apply Heq.
}
{ intro Heq; destruct p; term_simpl; repeat f_equal.
  + apply value_uncps_fmap; assumption.
  + apply value_uncps_fmap; assumption.
  + apply expr_uncps_fmap; assumption.
  + apply value_uncps_fmap; assumption.
  + apply value_uncps_fmap; assumption.
}
Qed.

Lemma expr_uncps_shift {κ} {Δ : T.VCtx} (e : T.expr Δ) :
  @expr_uncps (extC κ Δ) (shift e) = shift (expr_uncps e).
Proof.
  unfold shift; erewrite <- expr_uncps_fmap; reflexivity.
Qed.

Lemma value_uncps_shift {κ κ'} {Δ : T.VCtx} (v : T.valuelike κ Δ) :
  @value_uncps _ (extC κ' Δ) (shift v) = shift (value_uncps v).
Proof.
  unfold shift; erewrite <- value_uncps_fmap; reflexivity.
Qed.

Lemma program_uncps_shift {κ} {Δ : T.VCtx} (p : T.program Δ) :
  @program_uncps (extC κ Δ) (shift p) = shift (program_uncps p).
Proof.
  unfold shift; erewrite <- program_uncps_fmap; reflexivity.
Qed.

Fixpoint expr_uncps_bind {A B : T.VCtx}
    (f : Binding.Set.Sub (dom A) (dom B)) (g : Sub A B) (e : T.expr A) :
  (∀ x κ EQ, f x = value_uncps (g κ x EQ)) →
  bind f (expr_uncps e) = expr_uncps (bind g e)
with value_uncps_bind {κ} {A B : T.VCtx}
    (f : Binding.Set.Sub (dom A) (dom B)) (g : Sub A B) (v : T.valuelike κ A) :
  (∀ x κ EQ, f x = value_uncps (g κ x EQ)) →
  bind f (value_uncps v) = value_uncps (bind g v)
with program_uncps_bind {A B : T.VCtx}
    (f : Binding.Set.Sub (dom A) (dom B)) (g : Sub A B) (p : T.program A) :
  (∀ x κ EQ, f x = value_uncps (g κ x EQ)) →
  bind f (program_uncps p) = program_uncps (bind g p).
Proof.
{ intro Heq; destruct e; term_simpl; repeat f_equal.
  + erewrite <- program_uncps_bind; [ reflexivity | ].
    intros [ | x ] κ EQ; term_simpl; [ reflexivity | ].
    rewrite value_uncps_shift; f_equal; apply Heq.
  + apply value_uncps_bind; assumption.
  + apply value_uncps_bind; assumption.
}
{ intro Heq; destruct v; term_simpl; repeat f_equal.
  + apply Heq.
  + erewrite <- expr_uncps_bind; [ reflexivity | ].
    intros [ | x ] κ EQ; term_simpl; [ reflexivity | ].
    rewrite value_uncps_shift; f_equal; apply Heq.
  + erewrite <- program_uncps_bind; [ reflexivity | ].
    intros [ | x ] κ EQ; term_simpl; [ reflexivity | ].
    rewrite value_uncps_shift; f_equal; apply Heq.
}
{ intro Heq; destruct p; term_simpl; repeat f_equal.
  + apply value_uncps_bind; assumption.
  + apply value_uncps_bind; assumption.
  + apply expr_uncps_bind; assumption.
  + apply value_uncps_bind; assumption.
  + apply value_uncps_bind; assumption.
}
Qed.
