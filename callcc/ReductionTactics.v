Require Import Utf8.
Require Import Source.

(** Inside-out partial contexts for proofs by reflection *)
Inductive hctx (V : Set) : Set :=
| hctx_hole : hctx V
| hctx_app1 : hctx V → expr V → hctx V
| hctx_app2 : value V → hctx V → hctx V
.

Arguments hctx_hole {V}.
Arguments hctx_app1 {V} H e.
Arguments hctx_app2 {V} v H.

Fixpoint hplug {V : Set} (H : hctx V) (e : expr V) : expr V :=
  match H with
  | hctx_hole      => e
  | hctx_app1 H e' => hplug H (e_app e e')
  | hctx_app2 v H  => hplug H (e_app v e)
  end.

Fixpoint hrev {V : Set} (H : hctx V) (E : rctx V) : rctx V :=
  match H with
  | hctx_hole => E
  | hctx_app1 H e => hrev H (rctx_app1 E e)
  | hctx_app2 v H => hrev H (rctx_app2 v E)
  end.

Local Ltac auto_red_eval :=
  lazymatch goal with
  | [ |- pure_red (hplug _ (e_value _)) _ ] =>
    auto_red_cont
  | [ |- red (plug _ (e_value _)) _ ] =>
    auto_red_cont

  | [ |- pure_red (hplug ?H (e_app ?e1 ?e2)) ?er ] =>
    change (pure_red (hplug (hctx_app1 H e2) e1) er);
    auto_red_eval
  | [ |- red (plug ?F (e_app ?e1 ?e2)) ?er ] =>
    change (red (plug (ectx_app1 F e2) e1) er);
    auto_red_eval

  | [ |- red (plug ?F (e_callcc _)) _ ] =>
    apply red_callcc with (E := F)

  | [ |- red (plug ?F (e_abort _)) _ ] =>
    apply red_abort with (E := F)
  end

with auto_red_cont :=
  lazymatch goal with
  | [ |- pure_red (hplug (hctx_app1 ?H ?e2) (e_value ?v)) ?er ] =>
    change (pure_red (hplug (hctx_app2 v H) e2) er);
    auto_red_eval
  | [ |- red (plug (ectx_app1 ?F ?e2) (e_value ?v)) ?er ] =>
    change (red (plug (ectx_app2 v F) e2) er);
    auto_red_eval

  | [ |- pure_red (hplug (hctx_app2 ?v1 ?H) (e_value ?v2)) ?er ] =>
    apply pure_red_contr_in_rctx with (E := (hrev H rctx_hole));
    constructor
  | [ |- red (plug (ectx_app2 ?v1 ?F) (e_value ?v2)) ?er ] =>
    apply red_contr with (E := F);
    constructor

  | [ |- red (plug _ (e_value _)) _ ] => fail
  end.

Ltac auto_red :=
  simpl;
  lazymatch goal with
  | [ |- pure_red ?e1 ?e2 ] =>
    change (pure_red (hplug hctx_hole e1) e2);
    auto_red_eval
  | [ |- red (p_expr ?e1) ?p2 ] =>
    change (red (plug ectx_hole e1) p2);
    auto_red_eval
  | [ |- red (plug _ _) _ ] =>
    auto_red_eval
  end.
