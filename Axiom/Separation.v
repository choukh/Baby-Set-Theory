(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.

Axiom 分离 : 集合 → 性质 → 集合.
Axiom 分离公理 : ∀ A P x, x ∈ 分离 A P ↔ x ∈ A ∧ P x.
Notation "{ x ∊ A | P }" := (分离 A (λ x, P)) : 集合域.

Lemma 分离介入 : ∀ A (P : 性质), ∀x ∈ A, P x → x ∈ {x ∊ A | P x}.
Proof. intros. now apply 分离公理. Qed.

Lemma 分离除去 : ∀ A P, ∀x ∈ {x ∊ A | P x}, x ∈ A ∧ P x.
Proof. intros. now apply 分离公理 in H. Qed.

Lemma 分离之父集 : ∀ A P, ∀x ∈ {x ∊ A | P x}, x ∈ A.
Proof. intros. now apply 分离除去 in H. Qed.

Lemma 分离之条件 : ∀ A P, ∀x ∈ {x ∊ A | P x}, P x.
Proof. intros. now apply 分离除去 in H. Qed.
