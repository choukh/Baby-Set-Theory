(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Definition.Singleton.

Lemma 配对与顺序无关 : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. 外延.
  - apply 配对除去 in H as [].
    + rewrite H. auto.
    + rewrite H. auto.
  - apply 配对除去 in H as [].
    + rewrite H. auto.
    + rewrite H. auto.
Qed.

Lemma 配对与顺序无关' : ∀ a b, {a, b} = {b, a}.
Proof.
  intros. 外延.
  - apply 配对除去 in H as []; rewrite H; auto.
  - apply 配对除去 in H as []; rewrite H; auto.
Qed.

Lemma 配对相等 : ∀ a b c d,
  {a, b} = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c.
Proof.
  split; intros.
  - assert (Ha: a ∈ {c, d}). rewrite <- H. auto.
    assert (Hb: b ∈ {c, d}). rewrite <- H. auto.
    apply 配对除去 in Ha as [].
    + left. split.
      * auto.
      * apply 配对除去 in Hb as [].
        -- subst. now apply 单集配对相等 in H as [].
        -- auto.
    + right. split.
      * auto.
      * apply 配对除去 in Hb as [].
        -- auto.
        -- subst. now apply 单集配对相等 in H as [].
  - destruct H as [[]|[]].
    + subst. auto.
    + subst. apply 配对与顺序无关.
Qed.
