(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.

Notation "a ⋸ b" := (a ∈ b ∨ a = b) (at level 70) : 集合域.
