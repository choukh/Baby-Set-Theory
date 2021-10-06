(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.

Definition 传递集 := λ c, ∀ a b, a ∈ b → b ∈ c → a ∈ c.


