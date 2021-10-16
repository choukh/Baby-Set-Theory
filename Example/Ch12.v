(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.Function.

Print uniqueness.

Fact 为空的集合唯一 : uniqueness 为空.
Proof.
  intros x y Hx Hy. destruct 空集唯一 as [o [Ho H]].
  apply H in Hx, Hy. congruence.
Qed.

Check unique_existence.
(* unique_existence : ∀ (A : Type) (P : A → Prop),
  (∃ x : A, P x) ∧ uniqueness P ↔ (∃! x : A, P x) *)

Fact 为空的集合唯一' : uniqueness 为空.
Proof. apply unique_existence. apply 空集唯一. Qed.

Section 测试.
Variable 全称变量1 : 集合.
Variable 全称变量2 : 集合.

Lemma 测试命题 : 全称变量1 = 全称变量2.
Admitted.

End 测试.
Check 测试命题.
