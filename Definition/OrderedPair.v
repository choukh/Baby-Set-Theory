(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Intersect.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.BinaryIntersect.

Definition 有序对 := λ a b, {{a,}, {a, b}}.
Notation "< a , b , .. , c >" := ( 有序对 .. ( 有序对 a b ) .. c )
  (c at level 69, format "< a ,  b ,  .. ,  c >") : 集合域.

Theorem 有序对相等 : ∀ a b c d, <a, b> = <c, d> ↔ a = c ∧ b = d.
Proof.
  split; intros.
  - apply 配对相等 in H as [[]|[]].
    + apply 单集相等 in H; subst.
      apply 配对相等 in H0 as [[]|[]]; split; congruence.
    + apply 单集配对相等 in H as []. symmetry in H0.
      apply 单集配对相等 in H0 as []. split; congruence.
  - destruct H; congruence.
Qed.

Lemma 有序对之并 : ∀ a b, ⋃<a, b> = {a, b}.
Proof with auto.
  intros. 外延.
  - apply 并集除去 in H as [A [H1 H2]]. apply 配对除去 in H1 as []; subst...
    apply 单集除去 in H2; subst...
  - apply 配对除去 in H as []; subst. apply 左并介入... apply 右并介入...
Qed.

Lemma 有序对之交 : ∀ a b, ⋂<a, b> = {a,}.
Proof with auto.
  intros. unfold 有序对. 外延.
  - apply 交集除去 in H as [_ H]. apply H...
  - apply 单集除去 in H; subst. apply 交集介入. exists {a,}...
    intros x Hx. apply 配对除去 in Hx as []; subst...
Qed.

Definition 左 := λ p, ⋃ ⋂ p.
Definition 右 := λ p, ⋃ {x ∊ ⋃ p | x ∈ ⋂ p → ⋃ p = ⋂ p}.

Theorem 左投影 : ∀ a b, 左 <a, b> = a.
Proof. intros. unfold 左. rewrite 有序对之交. now rewrite 单集之并. Qed.

Theorem 右投影 : ∀ a b, 右 <a, b> = b.
Proof.
  intros. unfold 右. rewrite 有序对之并, 有序对之交. 外延.
  - apply 并集除去 in H as [A [HA Hx]].
    apply 分离除去 in HA as [H1 H2].
    apply 配对除去 in H1 as []; subst; auto.
    pose proof (H2 (单集介入 a)). symmetry in H.
    now apply 单集配对相等 in H as [_ H]; subst.
  - eapply 并集介入; eauto. apply 分离介入; auto.
    intros. now apply 单集除去 in H0; subst.
Qed.

Hint Rewrite 左投影 右投影 : core.
Ltac 化简 := autorewrite with core in *; try congruence.

Definition 为有序对 := λ p, ∃ x y, p = <x, y>.

Lemma 有序对为之 : ∀ x y, 为有序对 <x, y>.
Proof. intros. now exists x, y. Qed.
Global Hint Immediate 有序对为之 : core.

Definition 有序对分离 := λ A P, {p ∊ A | 为有序对 p ∧ P (左 p) (右 p)}.

Notation "{ ' < a , b > ∊ A | P }" := (有序对分离 A (λ a b, P))
  (a binder, b binder, format "{ ' < a ,  b >  ∊  A  |  P }") : 集合域.

Fact 有序对分离介入 : ∀ A (P : 集合 → 集合 → Prop) a b,
  <a, b> ∈ A → P a b → <a, b> ∈ {'<x, y> ∊ A | P x y}.
Proof. intros. apply 分离介入; firstorder. 化简. Qed.

Fact 有序对分离除去 : ∀ A P, ∀p ∈ {'<x, y> ∊ A | P x y},
  ∃ a b, <a, b> ∈ A ∧ P a b.
Proof.
  intros. apply 分离除去 in H as [Hp [[a [b Heq]] H]].
  subst. 化简. firstorder.
Qed.

Tactic Notation "有序对分离" "|-" ident(H) "for" simple_intropattern(a) simple_intropattern(b) "as" simple_intropattern(L) :=
  apply 分离除去 in H as [?Hp [[a [b ?Heqx]] L]]; subst; 化简.
Tactic Notation "有序对分离" "|-" ident(H) "for" simple_intropattern(a) simple_intropattern(b) :=
  有序对分离 |- H for ?a ?b as H.
  Tactic Notation "有序对分离" "|-" ident(H) "as" simple_intropattern(L) :=
  有序对分离 |- H for ?a ?b as L.
Tactic Notation "有序对分离" "|-" ident(H) := 有序对分离 |- H for ?a ?b as H.

Ltac 有序对分离介入1 a b := match goal with |- ?x ∈ _ => cut (x = <a, b>); [
  intros ?Heq; rewrite Heq; clear Heq; apply 分离介入; [auto|split; [auto|化简]]|
] end.

Ltac 有序对分离介入2 := match goal with |- <?a, ?b> ∈ _ =>
  apply 分离介入; [auto|split; [auto|化简]] end.

Tactic Notation "有序对分离" "-|" "with" constr(a) constr(b) := 有序对分离介入1 a b.
Tactic Notation "有序对分离" "-|" := 有序对分离介入2.
