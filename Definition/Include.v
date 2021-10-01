(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.

Notation "A ⊆ B" := (  ∀ x ∈ A, x ∈ B) (at level 70) : 集合域.
Notation "A ⊈ B" := (¬ ∀ x ∈ A, x ∈ B) (at level 70) : 集合域.

Lemma 包含自反 : ∀ A, A ⊆ A.
Proof. easy. Qed.

Lemma 包含传递 : ∀ A B C, A ⊆ B → B ⊆ C → A ⊆ C.
Proof. firstorder. Qed.

Lemma 包含反对称: ∀ A B, A ⊆ B → B ⊆ A → A = B.
Proof. intros. 外延; firstorder. Qed.

Notation "A ⊂ B" := (   A ⊆ B ∧ A ≠ B) (at level 70) : 集合域.
Notation "A ⊄ B" := (¬ (A ⊆ B ∧ A ≠ B)) (at level 70) : 集合域.

Lemma 包含则真包含或等于 : ∀ A B, A ⊆ B → A ⊂ B ∨ A = B.
Proof. intros. 排中 (A = B); firstorder. Qed.
