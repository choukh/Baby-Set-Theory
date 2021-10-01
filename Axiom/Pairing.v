(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Axiom 含配对集 : 集合 → 集合 → 集合.
Axiom 配对公理 : ∀ a b, a ∈ 含配对集 a b ∧ b ∈ 含配对集 a b.

Definition 配对 := λ a b, {x ∊ 含配对集 a b | x = a ∨ x = b}.
