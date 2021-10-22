(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Intersect.
Require Import BBST.Definition.Function.

(* 练习11-1 *)
Example 一对一符合直观 : ∀ f, 一对一 f →
  (∀x ∈ dom f, ∃!y, y = f[x]) ∧
  (∀y ∈ ran f, ∃!x ∈ dom f, y = f[x]). Admitted.

(* 练习11-2 *)
Theorem 完全格中的次序保持函数有最小不动点和最大不动点 :
  ∀ f A, f : 𝒫 A ⇒ 𝒫 A →
  (∀ X Y ∈ 𝒫 A, X ⊆ Y → f[X] ⊆ f[Y]) →
  let B := ⋂{X ∊ 𝒫 A | f[X] ⊆ X} in
  let C := ⋃{X ∊ 𝒫 A | X ⊆ f[X]} in
  f[B] = B ∧ f[C] = C ∧ ∀X ∈ 𝒫 A, f[X] = X → B ⊆ X ∧ X ⊆ C.
Proof with auto.
  intros * 映 保序 B C.
  apply 映射除去 in 映 as H. destruct H as [函 [定 值]].
  assert (A属: f[A] ⊆ A). admit.
  assert (B属: B ∈ 𝒫 A). admit.
  assert (C属: C ∈ 𝒫 A). admit.
  assert (B大: f[B] ⊆ B). admit.
  assert (C小: C ⊆ f[C]). admit.
  repeat split.
  - (* f[B] = B *) apply 包含的反对称性... admit.
  - (* f[C] = C *) apply 包含的反对称性... admit.
  - (* B ⊆ X *) intros x Hx. admit.
  - (* X ⊆ C *) intros x Hx. admit.
Admitted.
