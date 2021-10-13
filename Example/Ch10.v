(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Product.
Require Import BBST.Definition.Relation.
Require Import BBST.Definition.Function.

Check 关系.
(* 关系 : 集合 → 集合 → 关系类型 → 集合 *)

Check 函数.
(* 函数 : 集合 → 集合 → 函数类型 → 集合 *)

Fact 关系中的所有左边 : ∀ A B R, 为关系 A B R → ∀x ∈ A, ∀ y, <x, y> ∈ R → x ∈ ⋃⋃R.
Proof.
  intros. apply 并集介入 with {x,}; auto.
  apply 并集介入 with <x, y>; auto. apply 左配对介入.
Qed.

Fact 关系中的所有右边 : ∀ A B R, 为关系 A B R → ∀y ∈ B, ∀ x, <x, y> ∈ R → y ∈ ⋃⋃R.
Proof.
  intros. apply 并集介入 with {x, y}; auto.
  apply 并集介入 with <x, y>; auto. apply 右配对介入.
Qed.

(* 练习10-1 *)
Example 关系的全域: ∀ A B R, 为关系 A B R → fld R = ⋃⋃R. Admitted.

Example 练习10_2 : ∀ f g, 为函数 f → 为函数 g →
  f ⊆ g ↔ dom f ⊆ dom g ∧ ∀x ∈ dom f, f[x] = g[x]. Admitted.

Example 练习10_3: ∀ f g, 为函数 f → 为函数 g →
  f ⊆ g → dom g ⊆ dom f → f = g. Admitted.
