Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import Source.Syntax.
Require Import Relation_Operators.

Inductive contr {V : Set} : expr V → expr V → Prop :=
| contr_beta : ∀ e (v : value _),
    contr (e_app (v_lam e) v) (subst (Inc:=inc) e v)
.

(* ========================================================================= *)

Inductive pure_red {V : Set} : expr V → expr V → Prop :=
| pure_red_contr_in_rctx : ∀ E e e',
    contr e e' →
    pure_red (rplug E e) (rplug E e')
.

Notation pure_red_rtc e₁ e₂ := (clos_refl_trans_1n _ pure_red e₁ e₂).

Lemma pure_red_contr {V : Set} (e e' : expr V) :
  contr e e' → pure_red e e'.
Proof.
  apply pure_red_contr_in_rctx with (E := rctx_hole).
Qed.

Lemma pure_red_app1 {V : Set} (e e' : expr V) e₂ :
  pure_red e e' → pure_red (e_app e e₂) (e_app e' e₂).
Proof.
  destruct 1; apply pure_red_contr_in_rctx with (E := rctx_app1 _ _).
  assumption.
Qed.

Lemma pure_red_rtc_app1 {V : Set} (e e' : expr V) e₂ :
  pure_red_rtc e e' → pure_red_rtc (e_app e e₂) (e_app e' e₂).
Proof.
  induction 1; [ constructor | ].
  econstructor; [ | eassumption ].
  apply pure_red_app1; assumption.
Qed.

Lemma pure_red_app2 {V : Set} (v : value V) (e e' : expr V) :
  pure_red e e' → pure_red (e_app v e) (e_app v e').
Proof.
  destruct 1; apply pure_red_contr_in_rctx with (E := rctx_app2 _ _).
  assumption.
Qed.

Lemma pure_red_rtc_app2 {V : Set} (v : value V) (e e' : expr V) :
  pure_red_rtc e e' → pure_red_rtc (e_app v e) (e_app v e').
Proof.
  induction 1; [ constructor | ].
  econstructor; [ | eassumption ].
  apply pure_red_app2; assumption.
Qed.

(* ========================================================================= *)

Inductive red {V : Set} : program V → program V → Prop :=
| red_contr : ∀ E e e',
    contr e e' →
    red (plug E e) (plug E e')

| red_callcc : ∀ E e,
    red (plug E (e_callcc e))
        (plug E (subst (Inc:=inc) e
                   (v_lam (e_abort (plug (shift (Inc:=inc) E) (v_var VZ))))))

| red_abort : ∀ E p,
    red (plug E (e_abort p)) p
.

Notation red_rtc p₁ p₂ := (clos_refl_trans_1n _ red p₁ p₂).

Lemma red_in_ectx {V : Set} E (e e' : expr V) :
  pure_red e e' →
  red (plug E e) (plug E e').
Proof.
  destruct 1 as [ F e e' Hcontr ].
  revert E; induction F; intro E; simpl.
  + apply red_contr; assumption.
  + apply IHF with (E := ectx_app1 _ _).
  + apply IHF with (E := ectx_app2 _ _).
Qed.

Lemma red_rtc_in_ectx {V : Set} E (e e' : expr V) :
  pure_red_rtc e e' →
  red_rtc (plug E e) (plug E e').
Proof.
  induction 1; [ constructor | ].
  econstructor; [ | eassumption ].
  apply red_in_ectx; assumption.
Qed.

Definition terminates {V : Set} (p : program V) :=
  ∃ v : value V, red_rtc p v.
