(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Union.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Product.
Require Import BBST.Definition.Relation.

Notation 函数类型 := (集合 → 集合).
Definition 函数 := λ A B F, 关系 A B (λ x y, y = F x).

Fact 函数为关系 : ∀ A B F, 为关系 A B (函数 A B F).
Proof. intros * x H. 关系|-H; auto. Qed.

Definition 恒等函数 := λ A, 函数 A A (λ x, x).

Fact 恒等函数是恒等关系 : ∀ A, 恒等函数 A = 恒等关系 A.
Proof. intros. 外延; 关系|-H; 关系-|; auto. Qed.

Definition 单值 := λ f, ∀ x y z, <x, y> ∈ f → <x, z> ∈ f → y = z.
Definition 为函数 := λ f, 为序偶集 f ∧ 单值 f.

Fact 函数为之 : ∀ A B F, 为函数 (函数 A B F).
Proof.
  split. intros x H. 关系|-H; auto.
  intros x y z Hxy Hxz. 关系|-Hxy. 关系|-Hxz. congruence.
Qed.
Global Hint Immediate 函数为之 : core.

Fact 为函数则为关系 : ∀ f, 为函数 f → 为关系 (dom f) (ran f) f.
Proof. intros f H x Hx. apply 为序偶集即为关系; auto. apply H. Qed.

Definition 预应用 := λ f a, {'<x, y> ∊ f | x = a}.
Definition 应用 := λ f a, 右 ⋃ (预应用 f a).
Notation "f [ x ]" := (应用 f x) (at level 9, format "f [ x ]") : 集合域.

Lemma 函数预应用 : ∀ f x y, 为函数 f → <x, y> ∈ f → 预应用 f x = {<x, y>,}.
Proof with eauto.
  intros. 外延 w Hw.
  - 序偶分离|-Hw. subst x. replace y with b... eapply H...
  - 序偶分离-|x y. now apply 单集除去.
Qed.

Lemma 函数应用 : ∀ f x y, 为函数 f → <x, y> ∈ f → f[x] = y.
Proof.
  intros. unfold 应用. erewrite 函数预应用; eauto.
  rewrite 单集之并. 化简.
Qed.

Global Opaque 预应用 应用.

Fact 恒等函数应用 : ∀ A, ∀x ∈ A, (恒等函数 A)[x] = x.
Proof. intros. apply 函数应用. apply 函数为之. 关系-|; auto. Qed.

Lemma 函数介入0 : ∀ f x, 为函数 f → x ∈ dom f → <x, f[x]> ∈ f.
Proof. intros. 定|-H0 as [y Hp]. apply 函数应用 in Hp as Heq; congruence. Qed.

Lemma 函数介入1 : ∀ f x y, 为函数 f → x ∈ dom f → y = f[x] → <x, y> ∈ f.
Proof. intros. subst y. apply 函数介入0; auto. Qed.

Lemma 函数除去1 : ∀ f x y, 为函数 f → <x, y> ∈ f → <x, f[x]> ∈ f ∧ y = f[x].
Proof. intros. apply 函数应用 in H0 as Hap; auto. split; congruence. Qed.

Lemma 函数除去2 : ∀ f p, 为函数 f → p ∈ f → ∃ x, <x, f[x]> ∈ f ∧ p = <x, f[x]>.
Proof.
  intros * [偶集 单值] Hp. apply 偶集 in Hp as 偶. destruct 偶 as [a [b Heq]]. subst p.
  apply 函数应用 in Hp as Hap. 2: split; auto. exists a. split; congruence.
Qed.

Tactic Notation "函数" "|-" ident(H) "for" simple_intropattern(x) :=
  let Heq := fresh "Heq" in apply 函数除去2 in H as [x [H Heq]]; [rewrite Heq in *; clear Heq|try assumption].
Tactic Notation "函数" "|-" ident(H) :=
  first[函数|-H for ?x|apply 函数除去1 in H as [H Heq]; [rewrite Heq in *; clear Heq|try assumption]].
Tactic Notation "函数" "-|" := first[apply 函数介入0|apply 函数介入1]; try assumption.
Tactic Notation "函数" ident(H) := apply 函数介入0 in H.

Lemma 函数外延 : ∀ f g, 为函数 f → 为函数 g →
  dom f = dom g → (∀x ∈ dom f, f[x] = g[x]) → f = g.
Proof.
  intros * Hf Hg H1 H2. 外延 p Hp; 函数|-Hp; 定 Hp; 函数-|; auto; try congruence.
  symmetry. apply H2. congruence.
Qed.
