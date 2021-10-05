(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Pairing.

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
