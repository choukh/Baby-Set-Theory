(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Power.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OneTwo.

(* 练习4-1 *)
Fact 幂集之并含于并集之幂 : ∀ A B, 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B).
Proof.
Admitted.

(* 练习4-2 *)
Fact 元素之幂属于集合之并之幂之幂 : ∀ A, ∀a ∈ A, 𝒫 a ∈ 𝒫 𝒫 ⋃ A.
Proof.
Admitted.

(* 练习4-3 *)
Fact 零不为壹 : ∅ ≠ 壹.
Proof.
Admitted.

(* 练习4-4 *)
Fact 贰的元素的元素必为零 : ∀ a A, a ∈ A → A ∈ 贰 → a = ∅.
Proof.
Admitted.

(* 练习4-5 *)
Fact 小于贰的非空集合必为壹 : ∀A ∈ 贰, 非空 A → A = 壹.
Proof.
Admitted.

Fact 零并零的单集为壹 : ∅ ∪ {∅,} = 壹.
Proof. rewrite 空集左并. auto. Qed.

(* 练习4-6 *)
Fact 壹并壹的单集为贰 : 壹 ∪ {壹,} = 贰.
Proof.
  外延.
Admitted.
