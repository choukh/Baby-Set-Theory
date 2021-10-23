(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.

Definition 补集 := λ A B, {x ∊ A | x ∉ B}.
Notation "A - B" := (补集 A B) : 集合域.

Lemma 补集外介入 : ∀ A B x, x ∉ A ∨ x ∈ B → x ∉ A - B .
Proof.
  intros * []; intros H1.
  - apply H. now apply 分离之父集 in H1.
  - now apply 分离之条件 in H1.
Qed.

Lemma 补集外除去 : ∀ A B x, x ∉ A - B → x ∉ A ∨ x ∈ B.
Proof.
  intros. 排中 (x ∈ B). auto.
  left. intros H1. apply H. now apply 分离介入.
Qed.

Lemma 包含即补集为空 : ∀ A B, A ⊆ B ↔ A - B = ∅.
Proof with auto.
  split; intros.
  - apply 空集介入. intros x Hx. apply 分离除去 in Hx as []...
  - intros x Hx. 反证. apply 空集除去 with (A - B) x... now apply 分离介入.
Qed.

Lemma 补集是全集的子集 : ∀ A B, A - B ⊆ A.
Proof. intros * x H. now apply 分离之父集 in H. Qed.
Global Hint Immediate 补集是全集的子集 : core.

Lemma 真包含则补集非空 : ∀ A B, A ⊂ B → B - A ≠ ∅.
Proof.
  intros. apply 真包含则存在独有元素 in H as [x [Hx Hx']].
  apply 非空除去. exists x. apply 分离介入; auto.
Qed.

Lemma 补集反转包含关系 : ∀ A B C, A ⊆ B → C - B ⊆ C - A.
Proof.
  intros * H x Hx. apply 分离除去 in Hx as [Hx Hx']. apply 分离介入; auto.
Qed.

(* 右幺元 *)
Lemma 空集之补 : ∀ A, A - ∅ = A.
Proof.
  intros. 外延.
  - now apply 分离之父集 in H.
  - apply 分离介入. apply H. intros H0. 空集归谬.
Qed.

(* 左零元 *)
Lemma 补自空集 : ∀ A, ∅ - A = ∅.
Proof.
  intros. 外延.
  - apply 分离之父集 in H. 空集归谬.
  - 空集归谬.
Qed.
