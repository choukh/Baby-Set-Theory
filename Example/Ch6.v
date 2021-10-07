(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.TransitiveSet.

Theorem 传递集即其含于其幂 : ∀ A, 为传递集 A ↔ A ⊆ 𝒫 A.
Proof.
Admitted.
