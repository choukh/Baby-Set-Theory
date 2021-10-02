(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Include.

Definition 为空 := λ y, ∀ x, x ∉ y.

Lemma 存在空集 : ∃ y, 为空 y.
Proof.
  destruct 论域非空 as [A].
  exists {x ∊ A | x ≠ x}.
  intros x H. apply 分离之条件 in H.
  apply H. reflexivity.
Qed.

Lemma 空集唯一 : ∃! y, 为空 y.
Proof.
  destruct 存在空集 as [y Hy]. exists y. split.
  - apply Hy.
  - intros y' Hy'.
    外延 Hx; exfalso.
    + apply (Hy x). apply Hx.
    + apply (Hy' x). apply Hx.
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
Proof. intros. subst A. apply 空集定理. Qed.

Definition 非空 := λ A, ∃ x, x ∈ A.

Fact 空集非非空 : ¬ 非空 ∅.
Proof. intros H. destruct H as []. 空集归谬. Qed.

Lemma 非空介入 : ∀ A, A ≠ ∅ → 非空 A.
Proof.
  intros. 反证. apply H.
  assert (∀ x, x ∉ A). {
    intros x Hx. apply 反设. exists x. apply Hx.
  }
  now apply 空集介入 in H0.
Qed.

Lemma 非空除去 : ∀ A, 非空 A → A ≠ ∅.
Proof.
  intros A Hi H0. destruct Hi as [x Hx].
  rewrite H0 in Hx. 空集归谬.
Qed.

Lemma 空集排中 : ∀ A, A = ∅ ∨ 非空 A.
Proof.
  intros. 排中 (A = ∅).
  now left. right. now apply 非空介入.
Qed.

Lemma 空集含于任意 : ∀ A, ∅ ⊆ A.
Proof. intros A x Hx. 空集归谬. Qed.

Lemma 含于空即为空 : ∀ A, A ⊆ ∅ ↔ A = ∅.
Proof.
  split; intros Heq.
  - apply 空集介入. intros x Hx. apply Heq in Hx. 空集归谬.
  - subst. apply 空集含于任意.
Qed.
