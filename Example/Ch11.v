(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Function.

(* 练习11-1 *)
Example 一对一符合直观 : ∀ f, 一对一 f →
  (∀x ∈ dom f, ∃!y, y = f[x]) ∧
  (∀y ∈ ran f, ∃!x ∈ dom f, y = f[x]). Admitted.
