(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Power.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.BinaryUnion.

(* 练习4-1 *)
Fact 幂集之并含于并集之幂 : ∀ A B, 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B).
Proof.
Admitted.

(* 练习4-2 *)
Fact 元素之幂属于集合之并之幂之幂 : ∀ A, ∀a ∈ A, 𝒫 a ∈ 𝒫 𝒫 ⋃ A.
Proof.
Admitted.
