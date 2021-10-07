(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.TransitiveSet.

Notation "a ⋸ b" := (a ∈ b ∨ a = b) (at level 70) : 集合域.

Definition ϵ反自反 := λ A, ∀a ∈ A, a ∉ a.
Definition ϵ传递 := λ A, ∀ a b c ∈ A, a ∈ b → b ∈ c → a ∈ c.
Definition ϵ连通 := λ A, ∀ a b ∈ A, a ≠ b → a ∈ b ∨ b ∈ a.

Definition ϵ严格全序 := λ A, ϵ反自反 A ∧ ϵ传递 A ∧ ϵ连通 A.

Definition ϵ最小 := λ m A, m ∈ A ∧ ∀x ∈ A, m ⋸ x.

(* 任意非空子集有ϵ最小元 *)
Definition ϵ良序性 := λ A, ∀ X, 非空 X → X ⊆ A → ∃ m, ϵ最小 m X.

Definition ϵ良序 := λ A, ϵ严格全序 A ∧ ϵ良序性 A.
