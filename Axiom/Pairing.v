(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.

Axiom 含配对集 : 集合 → 集合 → 集合.
Axiom 配对公理 : ∀ a b, a ∈ 含配对集 a b ∧ b ∈ 含配对集 a b.

Definition 配对 := λ a b, {x ∊ 含配对集 a b | x = a ∨ x = b}.
Notation "{ a , b }" := (配对 a b) : 集合域.

Lemma 左配对介入 : ∀ a b, a ∈ {a, b}.
Proof. intros. apply 分离介入. apply 配对公理. now left. Qed.
Global Hint Immediate 左配对介入 : core.

Lemma 右配对介入 : ∀ a b, b ∈ {a, b}.
Proof. intros. apply 分离介入. apply 配对公理. now right. Qed.
Global Hint Immediate 右配对介入 : core.

Lemma 配对除去 : ∀ a b, ∀x ∈ {a, b}, x = a ∨ x = b.
Proof. intros. now apply 分离之条件 in H. Qed.

Lemma 配对顺序无关 : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. 外延; apply 配对除去 in H;
  destruct H; subst x; auto.
Qed.

Definition 单集 := λ a, {a, a}.
Notation "{ x , }" := (单集 x) (format "{ x , }") : 集合域.

Lemma 单集介入 : ∀ a, a ∈ {a,}.
Proof. intros. apply 左配对介入. Qed.
Global Hint Immediate 单集介入 : core.

Lemma 单集除去 : ∀ a b, a ∈ {b,} → a = b.
Proof. intros. now apply 配对除去 in H as []. Qed.

Lemma 单集外介入 : ∀ a b, a ≠ b → a ∉ {b,}.
Proof. intros * Hnq H. apply Hnq. now apply 单集除去 in H. Qed.

Lemma 单集外除去 : ∀ a b, a ∉ {b,} → a ≠ b.
Proof. intros * H Heq. apply H. subst. auto. Qed.

Lemma 单集配对相等 : ∀ a b c, {a,} = {b, c} → a = b ∧ b = c.
Proof.
  intros. assert (Hb: b ∈ {b, c}). auto.
  rewrite <- H in Hb. apply 单集除去 in Hb.
  assert (Hc: c ∈ {b, c}). auto.
  rewrite <- H in Hc. apply 单集除去 in Hc. split; congruence.
Qed.

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
    apply 配对顺序无关.
Qed.

Lemma 单集相等 : ∀ a b, {a,} = {b,} → a = b.
Proof. intros. now apply 单集配对相等 in H as []. Qed.
