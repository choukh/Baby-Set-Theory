(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.TransitiveSet.

Notation "a ⋸ b" := (a ∈ b ∨ a = b) (at level 70) : 集合域.

Definition ϵ反自反 := λ A, ∀a ∈ A, a ∉ a.
Definition ϵ传递 := λ A, ∀ a b c ∈ A, a ∈ b → b ∈ c → a ∈ c.
Definition ϵ连通 := λ A, ∀ a b ∈ A, a ≠ b → a ∈ b ∨ b ∈ a.

Definition ϵ偏序 := λ A, ϵ反自反 A ∧ ϵ传递 A.
Definition ϵ全序 := λ A, ϵ偏序 A ∧ ϵ连通 A.

Definition ϵq自反 := λ A, ∀a ∈ A, a ⋸ a.
Definition ϵq传递 := λ A, ∀ a b c ∈ A, a ⋸ b → b ⋸ c → a ⋸ c.
Definition ϵq反对称 := λ A, ∀ a b ∈ A, a ⋸ b → b ⋸ a → a = b.
Definition ϵq连通 := λ A, ∀ a b ∈ A, a ⋸ b ∨ b ⋸ a.

Definition ϵq偏序 := λ A, ϵq自反 A ∧ ϵq传递 A ∧ ϵq反对称 A.
Definition ϵq全序 := λ A, ϵq偏序 A ∧ ϵq连通 A.

Lemma ϵ连通即ϵq连通 : ∀ A, ϵ连通 A ↔ ϵq连通 A.
Proof with auto.
  split.
  - intros 连通 a Ha b Hb.
    排中 (a = b). left... apply 连通 in H as []...
  - intros 连通 a Ha b Hb H.
    destruct (连通 a Ha b Hb) as [[]|[]]...
    congruence. congruence.
Qed.

Definition ϵ非对称 := λ A, ∀ a b ∈ A, a ∈ b → b ∉ a.

Lemma ϵ偏序则ϵ非对称 : ∀ A, ϵ偏序 A → ϵ非对称 A.
Proof with auto.
  intros A [反自反 传递] a Ha b Hb 小于 大于.
  apply 反自反 with a... apply 传递 with b...
Qed.

Definition ϵ可换 := λ A, ∀ a b ∈ A, a ∈ b ↔ ¬ b ⋸ a.

Lemma ϵ全序则ϵ可换 : ∀ A, ϵ全序 A → ϵ可换 A.
Proof with auto.
  intros A [偏序 连通] a Ha b Hb. split.
  - intros 小于 [大于|等于].
    + apply ϵ偏序则ϵ非对称 with A a b...
    + subst. apply (proj1 偏序) with a...
  - intros 不大于等于.
    apply 德摩根定律 in 不大于等于 as [不大 不等].
    apply 连通 in 不等 as []... easy.
Qed.

Definition ϵ最小 := λ m A, m ∈ A ∧ ∀x ∈ A, m ⋸ x.
Notation 有ϵ最小元 A := (∃ m, ϵ最小 m A).
Notation 无ϵ最小元 A := (¬ 有ϵ最小元 A).
Notation 总有ϵ更小 A := (∀x ∈ A, ∃y ∈ A, y ∈ x).

Lemma ϵ全序则无ϵ最小元即总有ϵ更小 : ∀ A, ϵ全序 A → 无ϵ最小元 A ↔ 总有ϵ更小 A.
Proof with auto.
  intros A 全序. split.
  - intros 无最小 x Hx. 反证.
    apply 无最小. exists x. split...
    intros y Hy. 反证. apply 反设.
    exists y. split... apply ϵ全序则ϵ可换 with A...
  - intros 总有更小 [m [Hm 最小]].
    destruct (总有更小 m) as [n [Hn Hnm]]...
    apply ϵ全序则ϵ可换 with A n m...
Qed.

Definition ϵ良序性 := λ A, ∀ X, X ≠ ∅ → X ⊆ A → 有ϵ最小元 X.

Definition ϵ良序 := λ A, ϵ全序 A ∧ ϵ良序性 A.
