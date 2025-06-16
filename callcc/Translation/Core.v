Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import Common.

Definition VCtx_cps (V : Set) : T.VCtx :=
  {| dom   := V
  ;  arr _ := T.k_val
  |}.

Definition value_VCtx (Δ : T.VCtx) : Prop :=
  ∀ x, arr Δ x = T.k_val.

Lemma value_VCtx_mtC : value_VCtx mtC.
Proof. intros []. Qed.

Lemma value_VCtx_cps {V : Set} : value_VCtx (VCtx_cps V).
Proof. intro; reflexivity. Qed.

Lemma value_VCtx_ext {Δ : T.VCtx} (H : value_VCtx Δ) :
  value_VCtx (extC T.k_val Δ).
Proof.
  intros [ | x ]; [ reflexivity | apply H ].
Qed.

Local Notation V0 := (@T.v_var (extC _ _) _ VZ eq_refl).
Local Notation V1 := (@T.v_var (extC _ (extC _ _)) _ (VS VZ) eq_refl).
Local Notation V2 :=
  (@T.v_var (extC _ (extC _ (extC _ _))) _ (VS (VS VZ)) eq_refl).

Fixpoint expr_cps {Δ : T.VCtx} (H : value_VCtx Δ) (e : S.expr (dom Δ)) :
    T.expr Δ :=
  match e with
  | S.e_value v => T.e_lam (* k *)
      (T.p_appK (V0 (* k *))
                (shift (value_cps H v)))
  | S.e_app e₁ e₂ => T.e_lam (* k *)
      (T.p_appE (shift (expr_cps H e₁)) (T.v_clam (* f *)
      (T.p_appE (shift (shift (expr_cps H e₂))) (T.v_clam (* a *)
        (T.p_appE (T.e_app (V1 (* f *))
                          (V0 (* a *)))
                  (V2 (* k *)))))))
  | S.e_callcc e => T.e_lam (* k₀ *)
      (T.p_appK (T.v_clam (* k *)
                 (T.p_appE (fmap (lift mk_shift)
                             (expr_cps (value_VCtx_ext H) e))
                           (V1 (* k₀ *))))
                (T.v_vlam (* x *) (T.e_lam (* _ *)
                  (T.p_appK (V2 (* k₀ *))
                            (V1 (* x *))))))
  | S.e_abort p => T.e_lam (* _ *) (shift (program_cps H p))
  end

with value_cps {Δ : T.VCtx} (H : value_VCtx Δ) (v : S.value (dom Δ)) :
    T.value Δ :=
  match v with
  | S.v_var x => T.v_var x (H x)
  | S.v_lam e => T.v_vlam (expr_cps (value_VCtx_ext H) e)
  end

with program_cps {Δ : T.VCtx} (H : value_VCtx Δ) (p : S.program (dom Δ)) :
    T.program Δ :=
  match p with
  | S.p_expr e => T.p_appE (expr_cps H e) (T.v_clam (T.p_value V0))
  end.

Definition to_mtC : Arr (VCtx_cps ∅) mtC :=
  {| apply_arr (x : dom (VCtx_cps ∅)) := match x with end
  ;  arr_hom   (x : dom (VCtx_cps ∅)) := match x with end
  |}.

Definition to_extC {V : Set} :
    Arr (VCtx_cps (inc V)) (extC T.k_val (VCtx_cps V)) :=
  {| apply_arr (x : dom (VCtx_cps _)) := x : dom (extC _ _)
  ;  arr_hom x :=
      eq_trans (value_VCtx_ext value_VCtx_cps x) (eq_sym (value_VCtx_cps x))
  |}.

Definition VCtx_arr {V : Set} {Δ : T.VCtx}
  (H : value_VCtx Δ) (f : Binding.Set.Arr (dom Δ) V) :
    Arr Δ (VCtx_cps V) :=
  {| apply_arr := Binding.Set.apply_arr f : _ -> dom (VCtx_cps _)
  ;  arr_hom x := eq_sym (H x)
  |}.

Definition VCtx_sub {V : Set} {Δ : T.VCtx}
  (H : value_VCtx Δ) (f : Binding.Set.Sub (dom Δ) V) :
    Sub Δ (VCtx_cps V) :=
  {| apply_sub κ x EQ :=
      eq_rect T.k_val _
        (value_cps value_VCtx_cps (Binding.Set.apply_sub f x)) _
        (eq_trans (eq_sym (H x)) EQ)
  |}.

Definition ctx_shift {Δ : T.VCtx} {κ} (C : T.ctxE (extC κ Δ)) : T.ctxE Δ :=
  T.ctx_fmap mk_shift C.

Definition ctx_shiftv {Δ : T.VCtx} {κ} (C : T.ctxV (extC κ Δ)) : T.ctxV Δ :=
  T.ctx_fmapv mk_shift C.

Fixpoint ctx_cps {V : Set} (C : S.ctx V) : T.ctxE (VCtx_cps V) :=
  match C in S.ctx V return T.ctxE (VCtx_cps V) with
  | S.ctx_hole =>
      T.ctx_fmap to_mtC
                 (T.ctx_appE1 T.ctx_hole (T.v_clam (T.p_value V0)))
  | S.ctx_fmap f C =>
      T.ctx_fmap (VCtx_arr value_VCtx_cps f)
                 (ctx_cps C)
  | S.ctx_bind f C =>
      T.ctx_bind (VCtx_sub value_VCtx_cps f)
                 (ctx_cps C)
  | S.ctx_lam C =>
      T.ctx_fmap to_extC
                 (T.ctx_vlam (ctx_shiftv
                   (T.ctx_appK2 V0
                                (T.ctx_elam (ctx_cps C)))))
  | S.ctx_app1 C e₂ =>
      ctx_shift
        (T.ctx_appE1 (T.ctx_elam (ctx_cps C)) (T.v_clam (* f *)
          (T.p_appE (shift (shift (expr_cps value_VCtx_cps e₂)))
            (T.v_clam (* a *) (T.p_appE (T.e_app (V1 (* f *))
                                                 (V0 (* a *)))
                                        (V2 (* k *)))))))
  | S.ctx_app2 e₁ C =>
      ctx_shift (ctx_shift
        (T.ctx_appE1 (T.ctx_clam
            (T.ctx_appE2 (shift (expr_cps value_VCtx_cps e₁))
                         (T.ctx_elam (ctx_cps C))))
          (T.v_clam (* a *) (T.p_appE (T.e_app (V1 (* f *))
                                               (V0 (* a *)))
                                      (V2 (* k *))))))
  | S.ctx_callcc C =>
      T.ctx_fmap to_extC (T.ctx_fmap (lift mk_shift)
        (T.ctx_appE1
          (T.ctx_clam
            (T.ctx_appK1 (T.ctx_elam (ctx_cps C))
              (T.v_vlam (* x *) (T.e_lam (* _ *)
                                (T.p_appK (V2 (* k₀ *))
                                          (V1 (* x *)))))))
          V1))
  | S.ctx_abort C =>
      ctx_shift
        (T.ctx_appE1 (T.ctx_elam (ctx_cps C)) (T.v_clam (T.p_value V0)))
  end.
