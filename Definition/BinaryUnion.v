(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Union.

Require BBST.Axiom.Extensionality.
Require BBST.Definition.Include.
Require BBST.Definition.Emptyset.

Definition 二元并 := λ A B, ⋃{A, B}.
Notation "A ∪ B" := (二元并 A B) (at level 50) : 集合域.

Lemma 左并介入 : ∀ x A B, x ∈ A → x ∈ A ∪ B.
Proof.
  intros. eapply 并集介入. apply 左配对介入. auto.
Qed.

Lemma 右并介入 : ∀ x A B, x ∈ B → x ∈ A ∪ B.
Proof.
  intros. eapply 并集介入. apply 右配对介入. auto.
Qed.

Global Hint Immediate 左并介入 右并介入 : core.

Lemma 二元并除去 : ∀ x A B, x ∈ A ∪ B → x ∈ A ∨ x ∈ B.
Proof.
  intros. apply 并集除去 in H as [a [Ha Hx]].
  apply 配对除去 in Ha as []; subst; auto.
Qed.

Lemma 二元并外介入 : ∀ x A B, x ∉ A ∧ x ∉ B → x ∉ A ∪ B.
Proof.
  intros * [H1 H2] H. apply 二元并除去 in H as [].
  - now apply H1.
  - now apply H2.
Qed.

Lemma 二元并外除去 : ∀ x A B, x ∉ A ∪ B → x ∉ A ∧ x ∉ B.
Proof.
  intros. split; intros Hx; apply H; auto.
Qed.

Import BBST.Axiom.Extensionality.

Lemma 二元并幂等律 : ∀ A, A ∪ A = A.
Proof.
  intros. 外延; auto.
  apply 二元并除去 in H as []; auto.
Qed.

Lemma 二元并交换律 : ∀ A B, A ∪ B = B ∪ A.
Proof.
  intros. 外延;
  apply 二元并除去 in H as []; auto.
Qed.

Lemma 二元并的并等于并的二元并 : ∀ A B, ⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B).
Proof.
  intros. 外延.
  - apply 并集除去 in H as [y [Hy Hx]].
    apply 二元并除去 in Hy as [];
    [apply 左并介入|apply 右并介入]; eapply 并集介入; eauto.
  - apply 二元并除去 in H as [];
    apply 并集除去 in H as [y [H1 H2]]; eapply 并集介入; eauto.
Qed.

Import BBST.Definition.Include.

Lemma 二元并吸收律 : ∀ A B, A ⊆ B → A ∪ B = B.
Proof.
  intros. 外延; auto.
  apply 二元并除去 in H0 as []; auto.
Qed.

Import BBST.Definition.Emptyset.

Lemma 空集左并 : ∀ A, ∅ ∪ A = A.
Proof. intros. apply 二元并吸收律. apply 空集是任意集合的子集. Qed.

Lemma 空集右并 : ∀ A, A ∪ ∅ = A.
Proof. intros. rewrite 二元并交换律. apply 空集左并. Qed.

Lemma 二元并为空集 : ∀ A B, A ∪ B = ∅ → A = ∅ ∧ B = ∅.
Proof.
  intros.
  destruct (空集排中 A) as [HA|[a Ha]].
  destruct (空集排中 B) as [HB|[b Hb]].
  - now split.
  - exfalso. eapply 非空除去. 2: apply H.
    exists b. auto.
  - exfalso. eapply 非空除去. 2: apply H.
    exists a. auto.
Qed.
