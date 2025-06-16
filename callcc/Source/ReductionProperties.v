Require Import Utf8.
Require Import Source.Syntax.
Require Import Source.Reduction.

(* ========================================================================= *)
(* Composition with partial context *)

Fixpoint ectx_comp {V : Set} (F : ectx V) (E : rctx V) : ectx V :=
  match E with
  | rctx_hole     => F
  | rctx_app1 E e => ectx_comp (ectx_app1 F e) E
  | rctx_app2 v E => ectx_comp (ectx_app2 v F) E
  end.

Lemma ectx_comp_plug {V : Set} (F : ectx V) (E : rctx V) (e : expr V) :
  plug (ectx_comp F E) e = plug F (rplug E e).
Proof.
  revert F; induction E; simpl; intro F; try rewrite IHE; reflexivity.
Qed.

Lemma ectx_comp_hole {V : Set} (F : ectx V) E :
  ∃ FE, ectx_comp F E = ectx_comp ectx_hole FE.
Proof.
  revert E; induction F; simpl; intro E.
  + eexists; reflexivity.
  + apply IHF with (E := rctx_app1 _ _).
  + apply IHF with (E := rctx_app2 _ _).
Qed.

Lemma ectx_comp_hole' {V : Set} (F : ectx V) :
  ∃ E, F = ectx_comp ectx_hole E.
Proof.
  apply ectx_comp_hole with (E := rctx_hole).
Qed.

(* ========================================================================= *)
(* Potential redexes and unique decomposition *)

Inductive potential_redex {V : Set} : expr V → Prop :=
| pr_app : ∀ v₁ v₂ : value V,
    potential_redex (e_app v₁ v₂)
| pr_callcc : ∀ e,
    potential_redex (e_callcc e)
| pr_abort : ∀ p,
    potential_redex (e_abort p)
.

Lemma potential_redex_not_value {V : Set} (v : value V) :
  ¬ potential_redex v.
Proof.
  inversion 1.
Qed.

Lemma unique_partial_decomposition {V : Set}
    (E₁ E₂ : rctx V) (e₁ e₂ : expr V) :
  potential_redex e₁ → potential_redex e₂ →
  rplug E₁ e₁ = rplug E₂ e₂ → E₁ = E₂ ∧ e₁ = e₂.
Proof.
  intros He₁ He₂.
  revert E₂; induction E₁; intros []; simpl; intro Heq; auto; subst;
    repeat lazymatch goal with
    | [ H: potential_redex (e_app _ _) |- _ ] =>
      inversion H; clear H; subst
    | [ H: potential_redex (e_value _) |- _ ] =>
      exfalso; apply (potential_redex_not_value _ H)
    | [ H: e_value _ = rplug ?E _ |- _ ] =>
      destruct E; simpl in H; try discriminate; subst
    | [ H: rplug ?E _ = e_value _ |- _ ] =>
      destruct E; simpl in H; try discriminate; subst
    | [ H: e_app _ _ = e_app _ _ |- _ ] =>
      injection H; clear H; intros; subst
    | [ H: rplug _ _ = rplug _ _ |- _ ] =>
      apply IHE₁ in H; destruct H; subst; auto
    end.
Qed.

Lemma unique_decomposition {V : Set}
    (E₁ E₂ : ectx V) (e₁ e₂ : expr V) :
  potential_redex e₁ → potential_redex e₂ →
  plug E₁ e₁ = plug E₂ e₂ → E₁ = E₂ ∧ e₁ = e₂.
Proof.
  intros He₁ He₂ Heq.
  destruct (ectx_comp_hole' E₁) as [ E₁' Heq₁ ].
  destruct (ectx_comp_hole' E₂) as [ E₂' Heq₂ ]; subst.
  rewrite ectx_comp_plug, ectx_comp_plug in Heq; simpl in Heq.
  injection Heq; clear Heq; intro Heq.
  apply unique_partial_decomposition in Heq; try assumption; [].
  destruct Heq; split; subst; auto.
Qed.

Lemma contr_potential_redex {V : Set} (e₁ e₂ : expr V) :
  contr e₁ e₂ → potential_redex e₁.
Proof.
  destruct 1; constructor.
Qed.

(* ========================================================================= *)
(* Non-reducible terms *)

Lemma plug_value {V : Set} (E : ectx V) (e : expr V) (v : value V) :
  plug E e = v → E = ectx_hole ∧ e = v.
Proof.
  revert e; induction E; simpl; intros e₀ Heq.
  + injection Heq; auto.
  + edestruct IHE; [ eassumption | ]; discriminate.
  + edestruct IHE; [ eassumption | ]; discriminate.
Qed.

Lemma value_do_not_contr {V : Set} (v : value V) e :
  ¬ contr v e.
Proof.
  inversion 1.
Qed.

Lemma value_do_not_red {V : Set} (v : value V) p :
  ¬ red v p.
Proof.
  intro Hred; remember (p_expr v) as pv; destruct Hred;
    apply plug_value in Heqpv; destruct Heqpv; subst; try discriminate.
  eapply value_do_not_contr; eassumption.
Qed.

Ltac auto_potential_redex :=
  match goal with
  | [ |- potential_redex (e_app _ _)  ] => constructor
  | [ |- potential_redex (e_callcc _) ] => constructor
  | [ |- potential_redex (e_abort _)  ] => constructor
  | [ H: contr ?e _ |- potential_redex ?e ] =>
      eapply contr_potential_redex; eassumption
  end.

(* ========================================================================= *)
(* Properties of reduction *)

Lemma contr_deterministic {V : Set} (e e₁ e₂ : expr V) :
  contr e e₁ → contr e e₂ → e₁ = e₂.
Proof.
  destruct 1; inversion 1; reflexivity.
Qed.

Lemma red_deterministic_aux {V : Set} (p₁ p₂ p₁' p₂' : program V) :
  red p₁ p₁' → red p₂ p₂' → p₁ = p₂ → p₁' = p₂'.
Proof.
  intros [] [] Heq; apply unique_decomposition in Heq;
    try auto_potential_redex;
    destruct Heq; subst; try f_equal; try discriminate;
    lazymatch goal with
    | [ H1: contr ?e ?e1, H2: contr ?e ?e2 |- ?e1 = ?e2 ] =>
      eapply contr_deterministic; eassumption
    | [ H: e_callcc _ = e_callcc _ |- _ = _ ] =>
      injection H; clear H; intro; subst; reflexivity
    | [ H: e_abort _ = e_abort _ |- _ = _ ] =>
      injection H; clear H; intro; subst; reflexivity
    | [ H: contr (e_callcc _) _ |- _ ] => inversion H
    | [ H: contr (e_abort _) _ |- _ ] => inversion H
    end.
Qed.

Lemma red_deterministic {V : Set} (p p₁ p₂ : program V) :
  red p p₁ → red p p₂ → p₁ = p₂.
Proof.
  intros; eapply red_deterministic_aux; (eassumption || reflexivity).
Qed.
