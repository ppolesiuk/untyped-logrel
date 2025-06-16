Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import EquivLogicalRelation.Obs.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.Fundamental.
Require Import LogicalRelation.DefUnroll.

(* ========================================================================= *)
(** Soundness *)

Theorem rel_e_soundness {V : Set} (e₁ e₂ : expr V) :
  (∀n, n ⊨ rel_e e₁ e₂) → ctx_equiv e₁ e₂.
Proof.
  intros He C.
  apply Obs_adequacy; intro n.
  rewrite <- (bind_pure' (cplug C e₁)).
  rewrite <- (bind_pure' (cplug C e₂)).
  iapply (precongruence _ _ C n (He n)).
  iintro x; destruct x.
Qed.

(* ========================================================================= *)
(** Completeness *)

Definition ciu_equiv {V : Set} (e₁ e₂ : expr V) : Prop :=
  ∀ E (γ : V [⇒] ∅), obs_equiv (plug E (bind γ e₁)) (plug E (bind γ e₂)).

Fixpoint ctx_of_ectx (E : ectx ∅) : ctx ∅ :=
  match E with
  | ectx_hole     => ctx_hole
  | ectx_app1 E e => ctx_app1 (ctx_of_ectx E) e
  | ectx_app2 v E => ctx_app2 v (ctx_of_ectx E)
  end.

Lemma plug_ctx_of_ectx E e :
  cplug (ctx_of_ectx E) e = plug E e.
Proof.
  revert e; induction E; intro; simpl; reflexivity || apply IHE.
Qed.

Lemma ciu_completeness {V : Set} (e₁ e₂ : expr V) :
  ctx_equiv e₁ e₂ → ciu_equiv e₁ e₂.
Proof.
  intros He E γ.
  repeat rewrite <- plug_ctx_of_ectx.
  apply He with (C := ctx_bind _ _).
Qed.

Lemma ObsL_comp_obs_equiv p₂ p₃ n :
  obs_equiv p₂ p₃ → n ⊨ ∀ᵢ p₁, ObsL p₁ p₂ →ᵢ ObsL p₁ p₃.
Proof.
  intro Hobs; loeb_induction.
  iintros p₁ Hp.
  idestruct Hp as Hp_val Hp_red; idestruct Hp_val; isplit.
  + iintro.
    intros v₁ Hp₁; apply Hobs.
    eapply Hp_val; eassumption.
  + iintros p₁' Hred.
    iapply Hp_red in Hred; later_shift.
    apply ObsL_roll; iapply IH; apply ObsL_unroll; assumption.
Qed.

Lemma Obs_in_ObsL p₁ p₂ n :
  n ⊨ Obs p₁ p₂ → n ⊨ ObsL p₁ p₂.
Proof.
  apply I_conj_elim1.
Qed.

Lemma Obs_in_ObsL' p₁ p₂ n :
  n ⊨ Obs p₁ p₂ → n ⊨ ObsL p₂ p₁.
Proof.
  apply I_conj_elim2.
Qed.

Theorem rel_e_completeness {V : Set} (e₁ e₂ : expr V) n :
  ctx_equiv e₁ e₂ → n ⊨ rel_e e₁ e₂.
Proof.
  intro Hequiv; apply ciu_completeness in Hequiv.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE; isplit.
  + iapply ObsL_comp_obs_equiv; [ apply Hequiv | ].
    apply Obs_in_ObsL; iapply RelE_elim; [ | assumption ].
    iapply fundamental_property_e; assumption.
  + iapply ObsL_comp_obs_equiv; [ symmetry; apply Hequiv | ].
    apply Obs_in_ObsL'; iapply RelE_elim; [ | assumption ].
    iapply fundamental_property_e; assumption.
Qed.
