(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Include.

Fact 空集之分离 : ∀ P, {x ∊ ∅ | P x} = ∅.
Proof. intros P. apply 含于空集即为空集. auto. Qed.

(* 练习2-3 *)
Fact 分离为空集则全不满足 : ∀ A P, {x ∊ A | P x} = ∅ → ∀x ∈ A, ¬ P x.
Proof.
  intros A P H x Hx HP. eapply 空集除去.
Admitted.
