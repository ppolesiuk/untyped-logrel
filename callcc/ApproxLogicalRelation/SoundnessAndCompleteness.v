Require Import Utf8.
Require Import Binding.Lib Binding.Set.
Require Import IxFree.Lib IxFree.Nat.
Require Import Source.
Require Import ApproxLogicalRelation.Obs.
Require Import LogicalRelation.Core.
Require Import LogicalRelation.DefUnroll.
Require Import LogicalRelation.Fundamental.

(* ========================================================================= *)
(** Soundness *)

Theorem rel_e_soundness {V : Set} (e₁ e₂ : expr V) :
  (∀n, n ⊨ rel_e e₁ e₂) → ctx_approx e₁ e₂.
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

Definition ciu_approx {V : Set} (e₁ e₂ : expr V) : Prop :=
  ∀ E (γ : V [⇒] ∅), obs_approx (plug E (bind γ e₁)) (plug E (bind γ e₂)).

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
  ctx_approx e₁ e₂ → ciu_approx e₁ e₂.
Proof.
  intros He E γ.
  repeat rewrite <- plug_ctx_of_ectx.
  apply He with (C := ctx_bind _ _).
Qed.

Lemma Obs_comp_obs_approx p₁ p₂ p₃ n :
  obs_approx p₂ p₃ → (n ⊨ Obs p₁ p₂) → (n ⊨ Obs p₁ p₃).
Proof.
  intros Hobs1 Hobs2; idestruct Hobs2.
  + ileft; assumption.
  + idestruct Hobs2; iright; iintro; apply Hobs1; assumption.
Qed.

Theorem rel_e_completeness {V : Set} (e₁ e₂ : expr V) n :
  ctx_approx e₁ e₂ → n ⊨ rel_e e₁ e₂.
Proof.
  intro Hapx; apply ciu_completeness in Hapx.
  iintros γ₁ γ₂ Hγ E₁ E₂ HE.
  eapply Obs_comp_obs_approx; [ apply Hapx | ].
  iapply fundamental_property_e; assumption.
Qed.
