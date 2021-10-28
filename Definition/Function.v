(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Singleton.
Require Export BBST.Definition.Relation.

Notation 函数类型 := (集合 → 集合).
Definition 函数 := λ A B F, 关系 A B (λ x y, y = F x).

Fact 函数为关系 : ∀ A B F, 为关系 A B (函数 A B F).
Proof. intros * x H. 关系|-H; auto. Qed.

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
Notation "f [ x ]" := (应用 f x) (at level 7, format "f [ x ]") : 集合域.

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
  first[apply 函数除去1 in H as [H Heq]; [rewrite Heq in *; clear Heq|try assumption]|函数|-H for ?x].
Tactic Notation "函数" "-|" := first[apply 函数介入0|apply 函数介入1]; try assumption.
Tactic Notation "函数" ident(H) := apply 函数介入0 in H.

Lemma 函数之外延 : ∀ f g, 为函数 f → 为函数 g →
  dom f = dom g → (∀x ∈ dom f, f[x] = g[x]) → f = g.
Proof.
  intros * Hf Hg H1 H2. 外延 p Hp; 函数|-Hp; 定 Hp; 函数-|; auto; try congruence.
  symmetry. apply H2. congruence.
Qed.

Definition 单源 := λ f, ∀ x y z, <x, z> ∈ f → <y, z> ∈ f → x = y.
Definition 一对一 := λ f, 为函数 f ∧ 单源 f.

Fact 一对一为函数 : ∀ f, 一对一 f → 为函数 f.
Proof. firstorder. Qed.
Global Hint Immediate 一对一为函数 : core.

Lemma 一对一性质 : ∀ f, 一对一 f → ∀ x y ∈ dom f, f[x] = f[y] → x = y.
Proof with eauto.
  intros f [函数 单源] x Hx y Hy Heq.
  函数 Hx... 函数 Hy... rewrite Heq in Hx. eapply 单源...
Qed.

Definition 映射 := λ f A B, 为函数 f ∧ dom f = A ∧ ran f ⊆ B.
Notation "f : A ⇒ B" := (映射 f A B) (at level 60) : 集合域.

Definition 单射 := λ f A B, 一对一 f ∧ dom f = A ∧ ran f ⊆ B.
Notation "f : A ⇔ B" := (单射 f A B) (at level 60) : 集合域.

Definition 满射 := λ f A B, 为函数 f ∧ dom f = A ∧ ran f = B.
Notation "f : A ⟹ B" := (满射 f A B) (at level 60) : 集合域.

Definition 双射 := λ f A B, 一对一 f ∧ dom f = A ∧ ran f = B.
Notation "f : A ⟺ B" := (双射 f A B) (at level 60) : 集合域.

Lemma 映射介入 : ∀ f A B, 为函数 f → dom f = A → (∀x ∈ A, f[x] ∈ B) → f: A ⇒ B.
Proof with auto.
  intros * 函 定 值. split... split...
  intros y Hy. 值|-Hy as [x Hp]. 函数|-Hp. apply 值. rewrite <- 定. 域.
Qed.

Lemma 映射除去 : ∀ f A B, f: A ⇒ B → 为函数 f ∧ dom f = A ∧ ∀x ∈ A, f[x] ∈ B.
Proof with auto.
  intros * [函 [定 值]]. split... split...
  intros x Hx. rewrite <- 定 in Hx. 函数 Hx... apply 值. 域. 
Qed.

Lemma 单射即单源的映射 : ∀ f A B, f : A ⇔ B ↔ f : A ⇒ B ∧ 单源 f.
Proof. split; firstorder. Qed.

Definition 射满 := λ f A B, ∀y ∈ B, ∃x ∈ A, y = f[x].

Lemma 满射即射满的映射 : ∀ f A B, f: A ⟹ B ↔ f: A ⇒ B ∧ 射满 f A B.
Proof with auto. split.
  - intros [函 [定 值]]. split. split... split... rewrite 值...
    intros y Hy. rewrite <- 值 in Hy. 值|-Hy as [x Hp]. 函数|-Hp.
    exists x. split... rewrite <- 定. 域.
  - intros [[函 [定 值]] 射满]. split... split...
    apply 包含的反对称性... intros y Hy. apply 射满 in Hy as H.
    destruct H as [x [Hx Heq]]. 值-|x. 函数-|. congruence.
Qed.

Lemma 双射即单射且满射 : ∀ f A B, f: A ⟺ B ↔ f: A ⇔ B ∧ f: A ⟹ B.
Proof. unfold 单射, 包含. firstorder. congruence. Qed.

Lemma 双射即单源的满射 : ∀ f A B, f: A ⟺ B ↔ f: A ⟹ B ∧ 单源 f.
Proof. split; firstorder. Qed.

Lemma 双射即射满的单射 : ∀ f A B, f: A ⟺ B ↔ f: A ⇔ B ∧ 射满 f A B.
Proof with auto. split.
  - intros 单射. split. apply 双射即单射且满射...
    apply 满射即射满的映射, 双射即单射且满射...
  - intros [单射 射满]. apply 双射即单射且满射. split...
    apply 满射即射满的映射. split... apply 单射即单源的映射...
Qed.

Lemma 双射即单源射满的映射 : ∀ f A B, f: A ⟺ B ↔ f: A ⇒ B ∧ 单源 f ∧ 射满 f A B.
Proof with auto. split.
  - intros 双射. split. apply 单射即单源的映射, 双射即射满的单射...
    split. apply 双射. apply 双射即射满的单射...
  - intros [映射 [单源 射满]]. cut (f : A ⟹ B). firstorder.
    apply 满射即射满的映射...
Qed.

Definition 函数空间 := λ A B, {f ∊ 𝒫 (A × B) | f : A ⇒ B}.
Notation "A ⟶ B" := (函数空间 A B) (at level 60) : 集合域.

Lemma 函数是直积的子集 : ∀ f A B, f : A ⇒ B → f ⊆ A × B.
Proof.
  intros * [函 [定 值]] p Hp. 函数|-Hp. 直积-|.
  rewrite <- 定. 域. apply 值. 域.
Qed.

Lemma 函数空间介入 : ∀ f A B, f : A ⇒ B → f ∈ A ⟶ B.
Proof. intros. apply 分离介入; auto. now apply 幂集介入, 函数是直积的子集. Qed.

Lemma 函数空间除去 : ∀ f A B, f ∈ A ⟶ B → f : A ⇒ B.
Proof. intros. now apply 分离之条件 in H. Qed.
