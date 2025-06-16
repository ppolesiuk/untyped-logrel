Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Import Common Translation.Core.

Fixpoint expr_cps_fmap {A B : T.VCtx}
    (f : Arr A B) (g : Binding.Set.Arr (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (e : S.expr (dom A)) :
  (∀ x, f x = g x) →
  fmap f (expr_cps HA e) = expr_cps HB (fmap g e)
with value_cps_fmap {A B : T.VCtx}
    (f : Arr A B) (g : Binding.Set.Arr (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (v : S.value (dom A)) :
  (∀ x, f x = g x) →
  fmap f (value_cps HA v) = value_cps HB (fmap g v)
with program_cps_fmap {A B : T.VCtx}
    (f : Arr A B) (g : Binding.Set.Arr (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (p : S.program (dom A)) :
  (∀ x, f x = g x) →
  fmap f (program_cps HA p) = program_cps HB (fmap g p).
Proof.
{ intro Hfg; destruct e; term_simpl; repeat f_equal.
  + apply value_cps_fmap; assumption.
  + apply expr_cps_fmap; assumption.
  + apply expr_cps_fmap; assumption.
  + rewrite map_map_comp'.
    erewrite <- map_map_comp with (f := lift mk_shift) (g := lift f);
      [ | intros [ | x ]; reflexivity ].
    f_equal; apply expr_cps_fmap.
    intros [ | x ]; term_simpl; f_equal; apply Hfg.
  + apply program_cps_fmap; assumption.
}
{ intro Hfg; destruct v; term_simpl; repeat f_equal.
  + apply T.vvar_eq, Hfg.
  + apply expr_cps_fmap.
    intros [ | x ]; term_simpl; f_equal; apply Hfg.
}
{ intro Hfg; destruct p; term_simpl; repeat f_equal.
  + apply expr_cps_fmap; assumption.
}
Qed.

Fixpoint expr_cps_bind {A B : T.VCtx}
    (f : Sub A B) (g : Binding.Set.Sub (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (e : S.expr (dom A)) :
  (∀ x EQ, f _ x EQ = value_cps HB (g x)) →
  bind f (expr_cps HA e) = expr_cps HB (bind g e)
with value_cps_bind {A B : T.VCtx}
    (f : Sub A B) (g : Binding.Set.Sub (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (v : S.value (dom A)) :
  (∀ x EQ, f _ x EQ = value_cps HB (g x)) →
  bind f (value_cps HA v) = value_cps HB (bind g v)
with program_cps_bind {A B : T.VCtx}
    (f : Sub A B) (g : Binding.Set.Sub (dom A) (dom B))
    (HA : value_VCtx A) (HB : value_VCtx B) (p : S.program (dom A)) :
  (∀ x EQ, f _ x EQ = value_cps HB (g x)) →
  bind f (program_cps HA p) = program_cps HB (bind g p).
Proof.
{ intro Hfg; destruct e; term_simpl; repeat f_equal.
  + apply value_cps_bind; assumption.
  + apply expr_cps_bind; assumption.
  + apply expr_cps_bind; assumption.
  + erewrite bind_map_comm with (g₁ := lift f);
      [ f_equal; apply expr_cps_bind | ].
    - intros [ | x ] EQ; term_simpl; [ apply T.vvar_eq; reflexivity | ].
      rewrite Hfg.
      unfold shift; erewrite value_cps_fmap; reflexivity.
    - intros κ [ | x ] EQ; term_simpl; [ reflexivity | ].
      rewrite <- map_to_bind; term_simpl; repeat f_equal.
      apply T.KindDecEq.UIP.
  + apply program_cps_bind; assumption.
}
{ intro Hfg; destruct v; term_simpl; repeat f_equal.
  + apply Hfg.
  + apply expr_cps_bind.
    intros [ | x ] EQ; term_simpl; [ apply T.vvar_eq; reflexivity | ].
    rewrite Hfg; unfold shift; erewrite value_cps_fmap; reflexivity.
}
{ intro Hfg; destruct p; term_simpl; repeat f_equal.
  + apply expr_cps_bind; assumption.
}
Qed.

Lemma program_cps_cplug {V : Set} (C : S.ctx V) e :
  program_cps value_VCtx_mtC (S.cplug C e) =
  T.plugE (ctx_cps C) (expr_cps value_VCtx_cps e).
Proof.
  induction C; simpl; repeat f_equal; try rewrite IHC;
    term_simpl; repeat f_equal.
  + erewrite expr_cps_fmap, map_id'; [ reflexivity | intros [] ].
  + erewrite expr_cps_fmap; reflexivity.
  + erewrite expr_cps_bind; [ reflexivity | ].
    intros x EQ; simpl.
    match goal with
    | [ |- eq_rect _ _ _ _ ?H = _ ] =>
      rewrite (T.KindDecEq.UIP _ _ H eq_refl); reflexivity
    end.
  + erewrite expr_cps_fmap, map_id'; reflexivity.
  + erewrite expr_cps_fmap, map_id'; reflexivity.
Qed.
