(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Require BBST.Definition.Include.

Definition 为空 := λ y, ∀ x, x ∉ y.

Lemma 存在空集 : ∃ y, 为空 y.
Proof.
  destruct 论域非空 as [X].
  set {x ∊ X | False} as 空集.
  exists 空集. intros x H.
  now apply 分离之条件 in H.
Qed.

Lemma 空集唯一 : ∃! y, 为空 y.
Proof.
  destruct 存在空集 as [y Hy].
  exists y. unfold unique. split.
  - apply Hy.
  - intros y' Hy'. 外延.
    + exfalso. eapply Hy. apply H.
    + exfalso. eapply Hy'. apply H.
Qed.

Definition 空集 := 描述 为空.
Notation "∅" := 空集.

Theorem 空集定理 : 为空 ∅.
Proof. exact (描述公理 为空 空集唯一). Qed.

Ltac 空集归谬 := match goal with
  | H : ?x ∈ ∅ |- _ => exfalso; apply (空集定理 x); apply H
end.

Lemma 空集介入 : ∀ A, (∀ x, x ∉ A) → A = ∅.
Proof. intros. 外延. firstorder. 空集归谬. Qed.

Lemma 空集除去 : ∀ A, A = ∅ → (∀ x, x ∉ A).
Proof. intros. rewrite H. apply 空集定理. Qed.

Definition 非空 := λ A, ∃ x, x ∈ A.

Fact 空集非非空 : ¬ 非空 ∅.
Proof. intros []. 空集归谬. Qed.

Lemma 非空介入 : ∀ A, A ≠ ∅ → 非空 A.
Proof.
  intros. 反证. apply H.
  apply 空集介入. intros x Hx.
  apply 反设. exists x. apply Hx.
Qed.

Lemma 非空除去 : ∀ A, 非空 A → A ≠ ∅.
Proof.
  intros A [x Hx] H. rewrite H in Hx. 空集归谬.
Qed.

Lemma 空集排中 : ∀ A, A = ∅ ∨ 非空 A.
Proof.
  intros. 排中 (A = ∅). now left.
  right. now apply 非空介入.
Qed.

Import BBST.Definition.Include.

Lemma 空集是任意集合的子集 : ∀ A, ∅ ⊆ A.
Proof. intros A x Hx. 空集归谬. Qed.

Lemma 含于空集即为空集 : ∀ A, A ⊆ ∅ ↔ A = ∅.
Proof.
  split; intros H.
  - apply 空集介入. intros x Hx. apply H in Hx. 空集归谬.
  - rewrite H. apply 空集是任意集合的子集.
Qed.
