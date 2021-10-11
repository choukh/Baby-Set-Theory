(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Intersect.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.BinaryIntersect.
Require Import BBST.Definition.Complement.

Lemma 并交吸收律 : ∀ A B, A ∪ (A ∩ B) = A.
Proof with auto.
  intros. 外延... apply 二元并除去 in H as []...
  apply 二元交除去 in H as []...
Qed.

Lemma 交并吸收律 : ∀ A B, A ∩ (A ∪ B) = A.
Proof with auto.
  intros. 外延... apply 二元交除去 in H as []...
Qed.

Lemma 交并分配律 : ∀ A B C, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C).
Proof with auto.
  intros. 外延.
  - apply 二元并除去 in H as []...
    apply 二元交除去 in H as []...
  - apply 二元交除去 in H as [];
    apply 二元并除去 in H as [];
    apply 二元并除去 in H0 as []...
Qed.

Lemma 并交分配律 : ∀ A B C, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C).
Proof with auto.
  intros. 外延.
  - apply 二元交除去 in H as [].
    apply 二元并除去 in H as []...
  - apply 二元并除去 in H as [];
    apply 二元交除去 in H as []...
Qed.

Lemma 并补分配律 : ∀ A B C, (A ∪ B) - C = (A - C) ∪ (B - C).
Proof.
  intros. 外延.
  - apply 分离除去 in H as [Hx Hx'].
    apply 二元并除去 in Hx as [].
    + apply 左并介入. now apply 分离介入.
    + apply 右并介入. now apply 分离介入.
  - apply 二元并除去 in H as [];
    apply 分离除去 in H as [Hx Hx']; apply 分离介入; auto.
Qed.

Lemma 交补分配律 : ∀ A B C, (A ∩ B) - C = (A - C) ∩ (B - C).
Proof.
  intros. 外延.
  - apply 分离除去 in H as [Hx Hx'].
    apply 二元交除去 in Hx as [].
    apply 二元交介入; now apply 分离介入.
  - apply 二元交除去 in H as [].
    apply 分离除去 in H as [HxA HxC].
    apply 分离之父集 in H0. apply 分离介入; auto.
Qed.

Corollary 交补分配律_简化 : ∀ A B C, (A ∩ B) - C = A ∩ (B - C).
Proof.
  intros. rewrite 交补分配律. 外延.
  - apply 二元交除去 in H as []. apply 分离之父集 in H.
    apply 二元交介入; auto.
  - apply 二元交除去 in H as [H1 H2].
    apply 分离除去 in H2 as [Hx Hx'].
    apply 二元交介入; apply 分离介入; auto.
Qed.

Lemma 补并德摩根律 : ∀ A B C, C - (A ∪ B) = (C - A) ∩ (C - B).
Proof.
  intros. 外延.
  - apply 分离除去 in H as [Hx Hx'].
    apply 二元交介入; apply 分离介入; auto.
  - apply 二元交除去 in H as [H1 H2].
    apply 分离除去 in H1 as [Hx Hx']. apply 分离之条件 in H2.
    apply 分离介入; auto. now apply 二元并外介入.
Qed.

Lemma 补交德摩根律 : ∀ A B C, C - (A ∩ B) = (C - A) ∪ (C - B).
Proof.
  intros. 外延.
  - apply 分离除去 in H as [Hx Hx'].
    apply 二元交外除去 in Hx' as [].
    + apply 左并介入. now apply 分离介入.
    + apply 右并介入. now apply 分离介入.
  - apply 二元并除去 in H as [];
    apply 分离除去 in H as [Hx Hx'];
    apply 分离介入; auto; apply 二元交外介入; auto.
Qed.

Lemma 先补再并等于没补 : ∀ A B, A ∪ (B - A) = A ∪ B.
Proof with auto.
  intros. 外延.
  - apply 二元并除去 in H as []... apply 分离之父集 in H...
  - apply 二元并除去 in H as []...
    排中 (x ∈ A)... apply 右并介入. apply 分离介入...
Qed.

Lemma 先并再补等于没并 : ∀ A B, (A ∪ B) - A = B - A.
Proof with auto.
  intros. 外延; apply 分离除去 in H as [].
  - apply 二元并除去 in H as []. exfalso... apply 分离介入...
  - apply 分离介入...
Qed.

Lemma 并自身之补得全集 : ∀ A S, A ⊆ S → A ∪ (S - A) = S.
Proof with auto.
  intros. rewrite 先补再并等于没补. 外延...
  apply 二元并除去 in H0 as []; auto.
Qed.

Lemma 交自身之补得空集 : ∀ A S, A ∩ (S - A) = ∅.
Proof.
  intros. apply 空集介入. intros x H.
  apply 二元交除去 in H as [H1 H2].
  now apply 分离之条件 in H2.
Qed.
