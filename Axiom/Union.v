(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Require BBST.Definition.Include.
Require BBST.Definition.Emptyset.
Require BBST.Definition.Singleton.

Axiom 大并集 : 集合 → 集合.
Axiom 并集公理 : ∀ 𝒜, ∀A ∈ 𝒜, ∀x ∈ A, x ∈ 大并集 𝒜.

Definition 并集 := λ 𝒜, {x ∊ 大并集 𝒜 | ∃A ∈ 𝒜, x ∈ A}.
Notation "⋃ A" := (并集 A) (at level 8, right associativity) : 集合域.

Lemma 并集介入 : ∀ 𝒜, ∀A ∈ 𝒜, ∀a ∈ A, a ∈ ⋃ 𝒜.
Proof.
  intros 𝒜 A HA a Ha. apply 分离介入.
  eapply 并集公理; eauto. now exists A.
Qed.

Lemma 并集除去 : ∀ 𝒜, ∀a ∈ ⋃ 𝒜, ∃A ∈ 𝒜, a ∈ A.
Proof.
  intros 𝒜 a Ha. now apply 分离之条件 in Ha.
Qed.

Import BBST.Definition.Include.

Lemma 元素是并集的子集: ∀A, ∀a ∈ A, a ⊆ ⋃A.
Proof.
  intros A a Ha x Hx. eapply 并集介入; eauto.
Qed.

Lemma 并集保持包含关系 : ∀ A B, A ⊆ B → ⋃ A ⊆ ⋃ B.
Proof.
  intros A B H x Hx.
  apply 并集除去 in Hx as [b [Hb Hx]].
  eapply 并集介入; eauto.
Qed.

Lemma 所有元素都是子集则并集也是子集 : ∀ A B, (∀a ∈ A, a ⊆ B) → ⋃A ⊆ B.
Proof.
  intros A B H x Hx.
  apply 并集除去 in Hx as [b [Hb Hx]].
  eapply H; eauto.
Qed.

Import BBST.Definition.Emptyset.

Lemma 空集之并 : ⋃ ∅ = ∅.
Proof.
  外延. 2: 空集归谬.
  apply 并集除去 in H as [a [H _]]. 空集归谬.
Qed.

Import BBST.Definition.Singleton.

Lemma 单集之并 : ∀ x, ⋃ {x,} = x.
Proof.
  intros. 外延.
  - apply 并集除去 in H as [a [H1 H2]].
    apply 单集除去 in H1. congruence.
  - eapply 并集介入; eauto.
Qed.
