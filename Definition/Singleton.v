(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Pairing.

Require BBST.Axiom.Extensionality.
Require BBST.Definition.Include.
Require BBST.Definition.Emptyset.

Definition 单集 := λ a, {a, a}.
Notation "{ x , }" := (单集 x) (format "{ x , }") : 集合域.

Lemma 单集介入 : ∀ a, a ∈ {a,}.
Proof. intros. apply 左配对介入. Qed.

Lemma 单集除去 : ∀ a b, a ∈ {b,} → a = b.
Proof. intros. now apply 配对除去 in H as []. Qed.

Global Hint Immediate 单集介入 : core.

Lemma 单集外介入 : ∀ a b, a ≠ b → a ∉ {b,}.
Proof. intros * Hnq H. apply Hnq. now apply 单集除去 in H. Qed.

Lemma 单集外除去 : ∀ a b, a ∉ {b,} → a ≠ b.
Proof. intros * H Heq. apply H. rewrite Heq. auto. Qed.

Lemma 单集配对相等 : ∀ a b c, {a,} = {b, c} → a = b ∧ b = c.
Proof.
  intros.
  assert (Hc: c ∈ {b, c}). auto.
  assert (Hb: b ∈ {b, c}). auto.
  rewrite <- H in Hb. apply 单集除去 in Hb.
  rewrite <- H in Hc. apply 单集除去 in Hc.
  split; congruence.
Qed.

Lemma 单集相等 : ∀ a b, {a,} = {b,} → a = b.
Proof. intros. now apply 单集配对相等 in H as []. Qed.

Lemma 配对相等 : ∀ a b c d,
  {a, b} = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c.
Proof.
  split; intros.
  - assert (Ha: a ∈ {c, d}). rewrite <- H. auto.
    assert (Hb: b ∈ {c, d}). rewrite <- H. auto.
    apply 配对除去 in Ha as []; [left|right]; split; auto;
    apply 配对除去 in Hb as []; auto; subst;
    now apply 单集配对相等 in H as [].
  - destruct H as [[]|[]]; subst; auto.
    apply 配对与顺序无关.
Qed.

Import BBST.Axiom.Extensionality.

Lemma 所有元素都相等的集合是单集 : ∀ A, ∀x ∈ A, (∀y ∈ A, x = y) → A = {x,}.
Proof.
  intros A x Hx H. 外延 a Ha.
  - apply H in Ha. subst. auto.
  - apply 单集除去 in Ha. subst. easy.
Qed.

Import BBST.Definition.Include.

Lemma 元素的单集是原集合的子集 : ∀ A, ∀x ∈ A, {x,} ⊆ A.
Proof.
  intros A x Hx y Hy. apply 单集除去 in Hy. congruence.
Qed.

Import BBST.Definition.Emptyset.

Lemma 单集的子集是空集或该单集 : ∀ x A, A ⊆ {x,} → A = ∅ ∨ A = {x,}.
Proof.
  intros. destruct (空集排中 A) as [H0|[a Ha]].
  - left. apply H0.
  - right. apply 所有元素都相等的集合是单集.
    + apply H in Ha as Ha'. apply 单集除去 in Ha'. subst. easy.
    + intros b Hb. apply H in Hb. apply 单集除去 in Hb. easy.
Qed.
