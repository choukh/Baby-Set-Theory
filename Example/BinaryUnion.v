(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.RussellSet.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.

(* 练习3 *)
Fact 不存在所有单集的集合: ¬ ∃ A, ∀ a, {a,} ∈ A.
Proof.
Admitted.
