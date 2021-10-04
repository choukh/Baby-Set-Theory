(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.

Notation "A ⊆ B" := (  ∀x ∈ A, x ∈ B) (at level 70) : 集合域.
Notation "A ⊈ B" := (¬ ∀x ∈ A, x ∈ B) (at level 70) : 集合域.

(* 练习2-1 *)
Lemma 包含的自反性 : ∀ A, A ⊆ A.
Proof. easy. Qed.

Lemma 包含的传递性 : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof. firstorder. Qed.

Lemma 包含的反对称性: ∀ A B, A ⊆ B → B ⊆ A → A = B.
Proof. intros. 外延; firstorder. Qed.

Notation "A ⊂ B" := (   A ⊆ B ∧ A ≠ B) (at level 70) : 集合域.
Notation "A ⊄ B" := (¬ (A ⊆ B ∧ A ≠ B)) (at level 70) : 集合域.

(* 练习2-2 *)
Lemma 包含则真包含或等于 : ∀ A B, A ⊆ B → A ⊂ B ∨ A = B.
Proof. intros. 排中 (A = B); firstorder. Qed.

Lemma 真包含则存在独有元素 : ∀ A B, A ⊂ B → ∃x ∈ B, x ∉ A.
Proof.
  intros A B [Hsub Hneq]. apply 非全是即存非.
  intros Hsub'. apply Hneq. 外延; auto.
Qed.
