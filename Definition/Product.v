(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OrderedPair.

Lemma 包含直积的集合 : ∀ A B, ∀a ∈ A, ∀b ∈ B, <a, b> ∈ 𝒫 𝒫 (A ∪ B).
Proof.
  intros. apply 幂集介入. intros x Hx. apply 幂集介入. intros y Hy.
  apply 配对除去 in Hx as [].
  - subst. apply 单集除去 in Hy; subst; auto.
  - subst. apply 配对除去 in Hy as []; subst; auto.
Qed.

Definition 直积 := λ A B, {'<a, b> ∊ 𝒫 𝒫 (A ∪ B) | a ∈ A ∧ b ∈ B}.
Notation "A × B" := (直积 A B) (at level 40) : 集合域.

Lemma 直积介入 : ∀ A B, ∀a ∈ A, ∀b ∈ B, <a, b> ∈ A × B.
Proof. intros. 序偶分离-|; auto. apply 包含直积的集合; auto. Qed.
Global Hint Resolve 直积介入 : core.

Lemma 直积除去1 : ∀ A B a b, <a, b> ∈ A × B → a ∈ A ∧ b ∈ B.
Proof. intros. 序偶分离|-H. easy. Qed.

Lemma 直积除去2 : ∀ A B p, p ∈ A × B → ∃a ∈ A, ∃b ∈ B, p = <a, b>.
Proof. intros. 序偶分离|-H. firstorder. Qed.

Tactic Notation "直积" "|-" ident(H) "for" simple_intropattern(a) simple_intropattern(Ha) simple_intropattern(b) simple_intropattern(Hb) :=
  let Heq := fresh "Heq" in apply 直积除去2 in H as [a [Ha [b [Hb Heq]]]]; rewrite Heq in *; clear Heq; 化简.
Tactic Notation "直积" "|-" ident(H) "for" simple_intropattern(Ha) simple_intropattern(Hb):=
  first[直积|-H for ?a Ha ?b Hb|apply 直积除去1 in H as [Ha Hb]].
Tactic Notation "直积" "|-" ident(H) :=
  first[直积|-H for ?a ?Ha ?b ?Hb|apply 直积除去1 in H as [?Ha ?Hb]].
Tactic Notation "直积" "-|" constr(a) constr(b) :=
  match goal with |- ?x ∈ _ => cut (x = <a, b>); [
    intros ?Heq; rewrite Heq; clear Heq; apply 直积介入|
  ] end.
Tactic Notation "直积" "-|" := apply 直积介入.

Definition 为序偶集 := λ A, ∀p ∈ A, 为序偶 p.

Fact 直积为序偶集 : ∀ A B, 为序偶集 (A × B).
Proof. intros * p H. 直积|-H. auto. Qed.
Global Hint Immediate 直积为序偶集 : core.

Lemma 左积空集 : ∀ A, ∅ × A = ∅.
Proof. intros. apply 含于空集即为空集. intros x H. 直积|-H. 空集归谬. Qed.

Lemma 右积空集 : ∀ A, A × ∅ = ∅.
Proof. intros. apply 含于空集即为空集. intros x H. 直积|-H. 空集归谬. Qed.

Lemma 直积为空集 : ∀ A B, A × B = ∅ → A = ∅ ∨ B = ∅.
Proof with auto.
  intros.
  destruct (空集排中 A) as [|[a Ha]]...
  destruct (空集排中 B) as [|[b Hb]]...
  exfalso. apply (非空除去 (A × B))... exists <a, b>...
Qed.

Lemma 单集之积 : ∀ x, {x,} × {x,} = {<x, x>,}.
Proof with auto.
  intros. 外延.
  - 直积|-H. apply 单集除去 in Ha. apply 单集除去 in Hb. subst...
  - apply 单集除去 in H. subst...
Qed.

Lemma 积并分配律 : ∀ A B C, A × (B ∪ C) = (A × B) ∪ (A × C).
Proof with auto.
  intros. 外延.
  - 直积|-H. apply 二元并除去 in Hb as []...
  - apply 二元并除去 in H as []; 直积|-H...
Qed.

Lemma 并积分配律 : ∀ A B C, (A ∪ B) × C = (A × C) ∪ (B × C).
Proof with auto.
  intros. 外延.
  - 直积|-H. apply 二元并除去 in Ha as []...
  - apply 二元并除去 in H as []; 直积|-H...
Qed.
