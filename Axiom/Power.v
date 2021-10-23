(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Include.

Require BBST.Axiom.Extensionality.
Require BBST.Axiom.Union.
Require BBST.Axiom.Pairing.
Require BBST.Definition.Emptyset.
Require BBST.Definition.Singleton.

Axiom 大幂集 : 集合 → 集合.
Axiom 幂集公理 : ∀ A X, X ⊆ A → X ∈ 大幂集 A.

Definition 幂集 := λ A, {B ∊ 大幂集 A | B ⊆ A}.
Notation "'𝒫' A" := (幂集 A) (at level 9, right associativity, format "'𝒫'  A") : 集合域.

Lemma 幂集介入 : ∀ A B, B ⊆ A → B ∈ 𝒫 A.
Proof. intros. apply 分离介入; auto. now apply 幂集公理. Qed.

Lemma 幂集除去 : ∀ A B, B ∈ 𝒫 A → B ⊆ A.
Proof. intros. apply 分离之条件 in H; auto. Qed.

Lemma 任意集合都属于自身的幂集 : ∀ A, A ∈ 𝒫 A.
Proof. intros. now apply 幂集介入. Qed.
Global Hint Immediate 任意集合都属于自身的幂集 : core.

Lemma 幂集保持包含关系 : ∀ A B, A ⊆ B → 𝒫 A ⊆ 𝒫 B.
Proof.
  intros * H x Hx. apply 幂集介入.
  eapply 包含的传递性. 2: apply H. now apply 幂集除去 in Hx.
Qed.

Fact 幂集是单射: ∀ A B, 𝒫 A = 𝒫 B → A = B.
Proof.
  intros. apply 包含的反对称性.
  - apply 幂集除去. rewrite <- H; auto.
  - apply 幂集除去. rewrite H; auto.
Qed.

Import BBST.Definition.Emptyset.
Global Hint Immediate 空集是任意集合的子集 : core.

Lemma 空集属于任意幂集 : ∀ A, ∅ ∈ 𝒫 A.
Proof.
  intros. apply 分离介入; auto. apply 幂集公理; auto.
Qed.

Lemma 只有空集是空集的幂集 : ∀ x, x ∈ 𝒫 ∅ ↔ x = ∅.
Proof.
  split; intros.
  - apply 含于空集即为空集. now apply 幂集除去.
  - subst. apply 空集属于任意幂集.
Qed.

Import BBST.Axiom.Union.

Lemma 并集之幂 : ∀ A, A ⊆ 𝒫 ⋃ A.
Proof.
  intros A x H. apply 幂集介入. now apply 并得父集.
Qed.

Import BBST.Axiom.Extensionality.

Lemma 幂集之并 : ∀ A, ⋃ (𝒫 A) = A.
Proof.
  intros. 外延.
  - apply 并集除去 in H as [y [Hy Hx]].
    apply 幂集除去 in Hy; auto.
  - eapply 并集介入; auto.
Qed.

Import BBST.Axiom.Pairing.
Import BBST.Definition.Singleton.

Lemma 空集之幂 : 𝒫 ∅ = {∅,}.
Proof.
  外延.
  - apply 幂集除去 in H.
    apply 含于空集即为空集 in H. subst. auto.
  - apply 单集除去 in H. subst. auto.
Qed.

Lemma 单集之幂 : ∀ a, 𝒫 {a,} = {∅, {a,}}.
Proof.
  intros. 外延.
  - apply 幂集除去 in H.
    apply 单集的子集是空集或该单集 in H as []; subst; auto.
  - apply 配对除去 in H as []; subst; auto.
    apply 空集属于任意幂集.
Qed.
