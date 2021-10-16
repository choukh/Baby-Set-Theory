(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Function.
Require Import BBST.Lemma.MetaFunction.

Definition 恒等函数 := λ A, 函数 A A (λ x, x).

Fact 恒等函数是恒等关系 : ∀ A, 恒等函数 A = 恒等关系 A.
Proof. intros. 外延; 关系|-H; 关系-|; auto. Qed.

Fact 恒等函数应用 : ∀ A, ∀x ∈ A, (恒等函数 A)[x] = x.
Proof. intros. apply 函数应用. apply 函数为之. 关系-|; auto. Qed.

Lemma 恒等函数为一对一 : ∀ A, 一对一 (恒等函数 A).
Proof.
  split. apply 函数为之. intros x y z H1 H2.
  关系|-H1. 关系|-H2. congruence.
Qed.

Theorem 恒等函数是双射 : ∀ A, 恒等函数 A : A ⟺ A.
Proof. intros. apply 元双射; firstorder. Qed.

Lemma 空集为函数 : 为函数 ∅.
Proof. split. intros x H. 空集归谬. intros x y z H. 空集归谬. Qed.

Lemma 空函数的定义域为空集 : dom ∅ = ∅.
Proof. 外延. 定|-H as [y H]. 空集归谬. 空集归谬. Qed.

Lemma 空函数的值域为空集 : ran ∅ = ∅.
Proof. 外延. 值|-H as [w H]. 空集归谬. 空集归谬. Qed.

Lemma 定义域为空集的函数是空函数 : ∀ f, 为函数 f → dom f = ∅ → f = ∅.
Proof.
  intros. 外延 p Hp. 2: 空集归谬.
  函数|-Hp. 定 Hp. rewrite H0 in Hp. 空集归谬.
Qed.

Lemma 值域为空集的函数是空函数 : ∀ f, 为函数 f → ran f = ∅ → f = ∅.
Proof.
  intros. 外延 p Hp. 2: 空集归谬.
  函数|-Hp. 值 Hp. rewrite H0 in Hp. 空集归谬.
Qed.

Theorem 空函数是空集到任意集合的单射 : ∀ A, ∅: ∅ ⇔ A.
Proof.
  intros. repeat split.
  - intros x Hx. 空集归谬.
  - intros x y z Hxy. 空集归谬.
  - intros x y z Hxz. 空集归谬.
  - apply 空函数的定义域为空集.
  - intros y Hy. 值|-Hy as [x Hp]. 空集归谬.
Qed.

Theorem 空函数是空集到空集的双射 : ∅: ∅ ⟺ ∅.
Proof.
  apply 双射即射满的单射. split.
  apply 空函数是空集到任意集合的单射. intros x Hx. 空集归谬.
Qed.

Definition 常函数 := λ A a, 函数 A {a,} (λ _, a).

Lemma 常函数是映射 : ∀ A a, 常函数 A a: A ⇒ {a,}.
Proof. intros. apply 元映射. auto. Qed.

Lemma 常函数应用 : ∀ A a, ∀x ∈ A, (常函数 A a)[x] = a.
Proof. intros. unfold 常函数. rewrite 元应用; auto. Qed.

Lemma 定义域非空的常函数是满射 : ∀ A a, 非空 A → 常函数 A a : A ⟹ {a,}.
Proof.
  intros A a [x Hx]. apply 元满射. auto.
  intros y Hy. apply 单集除去 in Hy; subst. firstorder.
Qed.

Lemma 单点集为函数 : ∀ a b, 为函数 {<a, b>,}.
Proof.
  intros. split.
  - intros x Hx. apply 单集除去 in Hx. subst x; auto.
  - intros x y z Hxy Hxz. apply 单集除去 in Hxy, Hxz.
    apply 序偶相等 in Hxy as [], Hxz as []; subst; auto.
Qed.

Theorem 单点函数应用: ∀ a b, ∀x ∈ {a,}, {<a, b>,}[x] = b.
Proof.
  intros. apply 单集除去 in H; subst.
  symmetry. apply 函数除去1. apply 单点集为函数. auto.
Qed.

Lemma 单点集一对一 : ∀ a b, 一对一 {<a, b>,}.
Proof.
  intros. split. apply 单点集为函数.
  intros x y z Hxz Hyz. apply 单集除去 in Hxz, Hyz.
  apply 序偶相等 in Hxz as [], Hyz as []; subst; auto.
Qed.

Lemma 单点集的定义域 : ∀ a b, dom {<a, b>,} = {a,}.
Proof.
  intros. 外延 Hx.
  - 定|-Hx as [y Hp]. apply 单集除去 in Hp.
    apply 序偶相等 in Hp as []; subst; auto.
  - apply 单集除去 in Hx; subst. 定-|b; auto.
Qed.

Lemma 单点集的值域 : ∀ a b, ran {<a, b>,} = {b,}.
Proof.
  intros. 外延 y Hy.
  - 值|-Hy as [x Hp]. apply 单集除去 in Hp.
    apply 序偶相等 in Hp as []; subst; auto.
  - apply 单集除去 in Hy; subst. 值-|a; auto.
Qed.

Theorem 单点集是双射 : ∀ a b, {<a, b>,} : {a,} ⟺ {b,}.
Proof.
  intros. split. apply 单点集一对一. split.
  apply 单点集的定义域. apply 单点集的值域.
Qed.
