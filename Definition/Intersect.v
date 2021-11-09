(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Emptyset.

Require BBST.Axiom.Extensionality.
Require BBST.Definition.Include.
Require BBST.Definition.Singleton.

Definition 交集 := λ A, {x ∊ ⋃ A | ∀a ∈ A, x ∈ a}.
Notation "⋂ A" := (交集 A) (at level 9, right associativity) : 集合域.

Lemma 交集介入 : ∀ x A, 非空 A → (∀a ∈ A, x ∈ a) → x ∈ ⋂ A.
Proof.
  intros x A [y Hy] Hx. apply 分离介入; auto.
  eapply 并集介入; eauto.
Qed.

Lemma 交集除去 : ∀ A, ∀x ∈ ⋂ A, 非空 A ∧ ∀a ∈ A, x ∈ a.
Proof.
  intros. apply 分离除去 in H as [H1 H2]. split; auto.
  apply 并集除去 in H1 as [y [Hy _]]. now exists y.
Qed.

Import BBST.Definition.Include.

Lemma 交得子集 : ∀A, ∀a ∈ A, ⋂ A ⊆ a.
Proof. intros * Ha x Hx. eapply 交集除去; eauto. Qed.

Lemma 交集反转包含关系 : ∀ A B, 非空 A → A ⊆ B → ⋂ B ⊆ ⋂ A.
Proof.
  intros * 非空 包含 x Hx.
  apply 交集除去 in Hx as [[b Hb] Hx]. eapply 交集介入; auto.
Qed.

Lemma 所有元素都是子集则交集也是子集 : ∀ A B, (∀a ∈ A, a ⊆ B) → ⋂ A ⊆ B.
Proof.
  intros * H x Hx.
  apply 交集除去 in Hx as [[a Ha] Hx]. eapply H; eauto.
Qed.

Import BBST.Axiom.Extensionality.
Import BBST.Definition.Emptyset.

Lemma 空集之交 : ⋂ ∅ = ∅.
Proof.
  外延. 2: 空集归谬.
  apply 交集除去 in H as [H _].
  exfalso. apply 空集非非空. apply H.
Qed.

Import BBST.Definition.Singleton.

Lemma 单集之交 : ∀ x, ⋂ {x,} = x.
Proof with auto.
  intros. 外延.
  - apply 交集除去 in H as [_ H]. apply H...
  - apply 交集介入. exists x...
    intros y Hy. apply 单集除去 in Hy; subst...
Qed.
