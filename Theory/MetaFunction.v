(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Function.

Lemma 元定义域 : ∀ A B F, (∀x ∈ A, F x ∈ B) → dom (函数 A B F) = A.
Proof with auto.
  intros. 外延 Hx. 定|-Hx as [y Hp]. 关系|-Hp...
  定-|(F x). 关系-|...
Qed.

Lemma 元应用 : ∀ A B F, (∀x ∈ A, F x ∈ B) → ∀x ∈ A, (函数 A B F)[x] = F x.
Proof. intros. symmetry. apply 函数除去1; auto. 关系-|; auto. Qed.

Lemma 元映射 : ∀ A B F, (∀x ∈ A, F x ∈ B) → 函数 A B F : A ⇒ B.
Proof with auto.
  intros. apply 映射介入... apply 元定义域...
  intros x Hx. rewrite 元应用...
Qed.

Lemma 元单射 : ∀ A B F,
  (∀x ∈ A, F x ∈ B) →
  (∀ x1 x2 ∈ A, F x1 = F x2 → x1 = x2) →
  函数 A B F : A ⇔ B.
Proof with auto.
  intros * 元单值 元单源.
  apply 单射即单源的映射. split. apply 元映射...
  intros x y z Hxz Hyz. 关系|-Hxz. 关系|-Hyz. apply 元单源... congruence.
Qed.

Lemma 元满射 : ∀ A B F,
  (∀x ∈ A, F x ∈ B) → 
  (∀y ∈ B, ∃x ∈ A, y = F x) →
  函数 A B F : A ⟹ B.
Proof with auto.
  intros * 元单值 元射满.
  apply 满射即射满的映射. split. apply 元映射...
  intros y Hy. apply 元射满 in Hy as H. destruct H as [x [Hx Heq]].
  exists x. split... rewrite 元应用...
Qed.

Theorem 元双射 : ∀ A B F,
  (∀x ∈ A, F x ∈ B) →
  (∀ x1 x2 ∈ A, F x1 = F x2 → x1 = x2) →
  (∀y ∈ B, ∃x ∈ A, y = F x) →
  函数 A B F : A ⟺ B.
Proof.
  intros * 元单值 元单源 元射满. apply 双射即单射且满射.
  split. now apply 元单射. now apply 元满射.
Qed.
