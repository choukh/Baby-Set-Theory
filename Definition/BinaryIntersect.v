(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.

Require BBST.Axiom.Extensionality.
Require BBST.Definition.Intersect.
Require BBST.Definition.BinaryUnion.
Require BBST.Definition.Include.
Require BBST.Definition.Emptyset.

Definition 二元交 := λ A B, {x ∊ A | x ∈ B}.
Notation "A ∩ B" := (二元交 A B) (at level 49) : 集合域.

Lemma 二元交介入 : ∀ x A B, x ∈ A → x ∈ B → x ∈ A ∩ B.
Proof. intros. now apply 分离介入. Qed.
Global Hint Resolve 二元交介入 : core.

Lemma 二元交除去 : ∀ x A B, x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof. intros. now apply 分离除去 in H. Qed.

Lemma 二元交外介入 : ∀ x A B, x ∉ A ∨ x ∉ B → x ∉ A ∩ B.
Proof. intros. firstorder using 二元交除去. Qed.

Lemma 二元交外除去 : ∀ x A B, x ∉ A ∩ B → x ∉ A ∨ x ∉ B.
Proof. intros. 排中 (x ∈ A); auto. Qed.

Import BBST.Axiom.Extensionality.

Lemma 二元交幂等律 : ∀ A, A ∩ A = A.
Proof. intros. 外延; auto. apply 二元交除去 in H as []; auto. Qed.

Lemma 二元交交换律 : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. 外延; apply 二元交除去 in H as []; auto. Qed.

Lemma 二元交结合律 : ∀ A B C, (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof.
  intros. 外延; apply 二元交除去 in H as [].
  apply 二元交除去 in H as []; auto.
  apply 二元交除去 in H0 as []; auto.
Qed.

Import BBST.Definition.Include.

Lemma 二元交保持包含关系 : ∀ A B C, A ⊆ B → A ∩ C ⊆ B ∩ C.
Proof. intros. apply 二元交除去 in H0 as []; auto. Qed.

Lemma 二元交拒斥父集 : ∀ A B, A ⊆ B → A ∩ B = A.
Proof. intros. 外延; auto. apply 二元交除去 in H0 as []; auto. Qed.

Import BBST.Definition.Emptyset.

(* 零元 *)
Lemma 左交空集 : ∀ A, ∅ ∩ A = ∅.
Proof. intros. apply 二元交拒斥父集. apply 空集是任意集合的子集. Qed.

Lemma 右交空集 : ∀ A, A ∩ ∅ = ∅.
Proof. intros. rewrite 二元交交换律. apply 左交空集. Qed.

(* 幺元 *)
Lemma 左交全集 : ∀ A S, A ⊆ S → S ∩ A = A.
Proof. intros. 外延; auto. now apply 二元交除去 in H0 as []. Qed.

Lemma 右交全集 : ∀ A S, A ⊆ S → A ∩ S = A.
Proof. intros. rewrite 二元交交换律. now apply 左交全集. Qed.

Import BBST.Definition.Intersect.
Import BBST.Definition.BinaryUnion.

Lemma 二元并的交等于交的二元交 : ∀ A B, 非空 A → 非空 B → ⋂ (A ∪ B) = (⋂ A) ∩ (⋂ B).
Proof with auto.
  intros. 外延.
  - apply 交集除去 in H1 as [_ H1].
    apply 二元交介入; apply 交集介入; auto.
  - apply 二元交除去 in H1 as [H1 H2]. apply 交集介入.
    + destruct H as [a Ha]. exists a; auto.
    + intros a Ha. apply 二元并除去 in Ha as [].
      * apply 交集除去 in H1 as [_ H1]; auto.
      * apply 交集除去 in H2 as [_ H2]; auto.
Qed.
