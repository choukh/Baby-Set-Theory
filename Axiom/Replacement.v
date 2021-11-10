(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.

Require BBST.Axiom.Union.
Require BBST.Definition.Singleton.

Notation 函数类型 := (集合 → 集合).

Axiom 大替代 : 函数类型 → 集合 → 集合.
Axiom 替代公理 : ∀ (F : 函数类型) A, ∀x ∈ A, F x ∈ 大替代 F A.

Definition 替代 := λ F A, {y ∊ 大替代 F A | ∃x ∈ A, y = F x}.
Notation "{ F | x ∊ A }" := (替代 (λ x, F) A) : 集合域.

Lemma 替代介入_自动 : ∀ F A, ∀x ∈ A, F x ∈ {F x | x ∊ A}.
Proof.
  intros. apply 分离介入.
  now apply 替代公理. now exists x.
Qed.
Global Hint Immediate 替代介入_自动 : core.

Lemma 替代介入 : ∀ F A y, (∃x ∈ A, y = F x) → y ∈ {F x | x ∊ A}.
Proof.
  intros. apply 分离介入. 2: auto.
  destruct H as [x [Hx Hy]]. subst. now apply 替代公理.
Qed.

Lemma 替代除去 : ∀ F A, ∀y ∈ {F x | x ∊ A}, ∃x ∈ A, y = F x.
Proof. intros. now apply 分离之条件 in H. Qed.

Global Opaque 替代.

Lemma 替代之外延 : ∀ F G A, (∀x ∈ A, F x = G x) → {F x | x ∊ A} = {G x | x ∊ A}.
Proof with auto.
  intros. 外延 y Hy; apply 替代除去 in Hy as [x [Hx Hy]]; subst.
  rewrite H... rewrite <- H...
Qed.

Lemma 替代改写 : ∀ {F G A}, (∀x ∈ A, F x = G x) → {F x | x ∊ A} = {G x | x ∊ A}.
Proof. exact 替代之外延. Qed.

Lemma 空集之替代 : ∀ F, {F x | x ∊ ∅} = ∅.
Proof.
  intros. apply 空集介入. intros y Hy.
  apply 替代除去 in Hy as [x [Hx _]]. 空集归谬.
Qed.

Lemma 仅空集之替代为空集 : ∀ F A, {F x | x ∊ A} = ∅ → A = ∅.
Proof.
  intros. apply 含于空集即为空集. intros x Hx.
  assert (F x ∈ {F x | x ∊ A}); auto.
  rewrite H in H0. 空集归谬.
Qed.

Import BBST.Definition.Singleton.

Lemma 全零替代为一 : ∀ F A, A ≠ ∅ → (∀x ∈ A, F x = ∅) → {F x | x ∊ A} = {∅,}.
Proof with auto.
  intros * H0 H. 外延 y Hy.
  - apply 替代除去 in Hy as [x [Hx Hy]]. subst. rewrite H...
  - apply 非空介入 in H0 as [a Ha]. apply 单集除去 in Hy. subst. rewrite <- (H a)...
Qed.

Lemma 仅全零替代为一 : ∀ F A, {F x | x ∊ A} = {∅,} → ∀x ∈ A, F x = ∅.
Proof with auto.
  intros F A H x Hx. 反证.
  assert (F x ∈ {∅,}). rewrite <- H...
  apply 单集除去 in H0...
Qed.

Export BBST.Axiom.Union.

Lemma 集族并介入 : ∀ F A, ∀x ∈ A, ∀y ∈ F x, y ∈ ⋃{F x | x ∊ A}.
Proof. intros. apply 并集介入 with (F x); auto. Qed.

Lemma 集族并除去 : ∀ F A, ∀y ∈ ⋃{F x | x ∊ A}, ∃x ∈ A, y ∈ F x.
Proof.
  intros F A y Hy.
  apply 并集除去 in Hy as [x [Hx Hy]].
  apply 替代除去 in Hx as [z [Hz Hx]]. subst. now exists z.
Qed.

Lemma 集族并为零 : ∀ F A, ⋃{F x | x ∊ A} = ∅ → A = ∅ ∨ ∀x ∈ A, F x = ∅.
Proof.
  intros. apply 仅零或一之并为零 in H as [].
  - apply 仅空集之替代为空集 in H; auto.
  - right. intros x Hx. eapply 仅全零替代为一 in H; eauto.
Qed.
