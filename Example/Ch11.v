(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Intersect.
Require Import BBST.Definition.Function.

(* 练习11-1 *)
Example 一对一符合直观 : ∀ f, 一对一 f →
  (∀x ∈ dom f, ∃!y, y = f[x]) ∧
  (∀y ∈ ran f, ∃!x ∈ dom f, y = f[x]). Admitted.

(* 练习11-2 *)
Theorem 次序保持函数在完全格中有最小不动点和最大不动点 :
  ∀ f A, f : 𝒫 A ⇒ 𝒫 A →
  (∀ X Y ∈ dom f, X ⊆ Y → f[X] ⊆ f[Y]) →
  let B := ⋂{X ∊ dom f | f[X] ⊆ X} in
  let C := ⋃{X ∊ dom f | X ⊆ f[X]} in
  f[B] = B ∧ f[C] = C ∧ ∀X ∈ dom f, f[X] = X → B ⊆ X ∧ X ⊆ C.
Admitted.
