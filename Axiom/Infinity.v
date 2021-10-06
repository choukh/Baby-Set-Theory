(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Successor.

Definition 归纳的 := λ A, ∅ ∈ A ∧ ∀a ∈ A, a⁺ ∈ A.

Axiom 𝐈 : 集合.
Axiom 无穷公理 : 归纳的 𝐈.
