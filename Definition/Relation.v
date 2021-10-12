(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Product.

Definition 关系 := λ A B P, {'<a, b> ∊ A × B | P a b}.

Definition 为关系 := λ A B R, R ⊆ A × B.

Fact 直积为关系 : ∀ A B, 为关系 A B (A × B).
Proof. firstorder. Qed.

Fact 直积之分离为关系 : ∀ A B P, 为关系 A B {p ∊ A × B | P p}.
Proof. intros * x Hx. apply 分离之父集 in Hx. auto. Qed.

Fact 关系为之 : ∀ A B P, 为关系 A B (关系 A B P).
Proof. intros. apply 直积之分离为关系. Qed.

Global Hint Immediate 直积为关系 直积之分离为关系 关系为之 : core.

Definition 关系类型 := 集合 → 集合 → Prop.

Lemma 关系介入 : ∀ A B (P : 关系类型), ∀a ∈ A, ∀b ∈ B, P a b → <a, b> ∈ 关系 A B P.
Proof. intros. 序偶分离-|; auto. Qed.

Lemma 关系除去1 : ∀ A B P a b, <a, b> ∈ 关系 A B P → a ∈ A ∧ b ∈ B ∧ P a b.
Proof. intros. 序偶分离|-H. 直积|-Hp. easy. Qed.

Lemma 关系除去2 : ∀ A B P x, x ∈ 关系 A B P → ∃a ∈ A, ∃b ∈ B, x = <a, b> ∧ P a b.
Proof.
  intros. 序偶分离|-H.
  apply 直积除去2 in Hp as [c [Hc [d [Hd Heq]]]].
  apply 序偶相等 in Heq as []; subst; firstorder.
Qed.

Tactic Notation "关系" "|-" ident(H) "for" simple_intropattern(a) simple_intropattern(Ha) simple_intropattern(b) simple_intropattern(Hb) :=
  let Heq := fresh "Heq" in apply 关系除去2 in H as [a [Ha [b [Hb [Heq H]]]]]; rewrite Heq in *; clear Heq; 化简.
Tactic Notation "关系" "|-" ident(H) "for" simple_intropattern(Ha) simple_intropattern(Hb) :=
  first[关系|-H for ?a Ha ?b Hb|apply 关系除去1 in H as [Ha [Hb H]]].
Tactic Notation "关系" "|-" ident(H) :=
  first[关系|-H for ?a ?Ha ?b ?Hb|apply 关系除去1 in H as [?Ha [?Hb H]]].
Tactic Notation "关系" "-|" constr(a) constr(b) := 序偶分离-|a b; [直积-||].
Tactic Notation "关系" "-|" := 序偶分离-|.

Definition 定义域 := λ R, {x ∊ ⋃⋃R | ∃ y, <x, y> ∈ R}.
Notation dom := 定义域.

Definition 值域 := λ R, {y ∊ ⋃⋃R | ∃ x, <x, y> ∈ R}.
Notation ran := 值域.

Definition 全域 := λ R, dom R ∪ ran R.
Notation fld := 全域.

Lemma 定义域介入 : ∀ R x y, <x, y> ∈ R → x ∈ dom R.
Proof with auto.
  intros. apply 分离介入.
  - apply 并集介入 with {x, y}...
    apply 并集介入 with <x, y>... apply 右配对介入.
  - exists y...
Qed.

Lemma 值域介入 : ∀ R x y, <x, y> ∈ R → y ∈ ran R.
Proof with auto.
  intros. apply 分离介入.
  - apply 并集介入 with {x, y}...
    apply 并集介入 with <x, y>... apply 右配对介入.
  - exists x...
Qed.

Lemma 定义域除去 : ∀ R, ∀x ∈ dom R, ∃ y, <x, y> ∈ R.
Proof. intros R x Hx. now apply 分离之条件 in Hx. Qed.

Lemma 值域除去 : ∀ R, ∀y ∈ ran R, ∃ x, <x, y> ∈ R.
Proof. intros R x Hx. now apply 分离之条件 in Hx. Qed.

Global Opaque 定义域 值域.

Fact 关系之定义域 : ∀ A B P, dom (关系 A B P) ⊆ A.
Proof. intros. apply 定义域除去 in H as [y H]. now 关系|-H. Qed.

Fact 关系之值域 : ∀ A B P, ran (关系 A B P) ⊆ B.
Proof. intros. apply 值域除去 in H as [w H]. now 关系|-H. Qed.

Definition 恒等关系 := λ A, 关系 A A (λ x y, x = y).

Fact 空集上的恒等关系为空集 : 恒等关系 ∅ = ∅.
Proof. 外延. 关系|-H. 空集归谬. 空集归谬. Qed.
