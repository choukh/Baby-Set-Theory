(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Replacement.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.BinaryIntersect.
Require Import BBST.Definition.Function.
Require Import BBST.Definition.Restriction.
Require Import BBST.Lemma.BasicFunction.

Lemma 函数之二元并 : ∀ f g, 为函数 f → 为函数 g →
  (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ↔ 为函数 (f ∪ g).
Proof with eauto.
  intros * Hf Hg. split; intros.
  - split.
    + (* 为序偶集 *) intros p Hp. apply 二元并除去 in Hp as [].
      apply Hf in H0... apply Hg in H0...
    + (* 单值 *) intros x y z Hxy Hxz.
      apply 二元并除去 in Hxy as [];
      apply 二元并除去 in Hxz as []; [eapply Hf| | |eapply Hg]...
      * 函数|-H0. 函数|-H1. apply H. apply 二元交介入; 域.
      * 函数|-H0. 函数|-H1. symmetry. apply H. apply 二元交介入; 域.
  - apply 二元交除去 in H0 as []. 函数 H0... 函数 H1...
    eapply H. apply 左并介入... apply 右并介入...
Qed.

Lemma 函数之二元并之定义域 : ∀ f g, 为函数 f → 为函数 g →
  dom (f ∪ g) = dom f ∪ dom g.
Proof with auto.
  intros * Hf Hg. 外延.
  - 定|-H as [y H]. apply 二元并除去 in H as [].
    apply 左并介入. 域. apply 右并介入. 域.
  - apply 二元并除去 in H as [].
    + 定|-H as [y H]. 定-|y. apply 左并介入...
    + 定|-H as [y H]. 定-|y. apply 右并介入...
Qed.

Lemma 函数加点 : ∀ f a b, 为函数 f → a ∉ dom f → 为函数 (f ∪ {<a, b>,}).
Proof with eauto.
  intros f a b Hf 域外.
  apply 函数之二元并... apply 单点集为函数.
  intros x Hx. exfalso. apply 二元交除去 in Hx as [].
  rewrite 单点集的定义域 in H0. apply 单集除去 in H0; subst...
Qed.

Lemma 函数加点之定义域 : ∀ f a b, dom (f ∪ {<a, b>,}) = dom f ∪ {a,}.
Proof with eauto.
  intros f a b. 外延.
  - 定|-H as [y H]. apply 二元并除去 in H as [].
    + 定 H. apply 左并介入...
    + apply 单集除去 in H. apply 序偶相等 in H as []; subst...
  - apply 二元并除去 in H as [].
    + 定|-H as [y H]. 定-|y. apply 左并介入...
    + apply 单集除去 in H. subst. 定-|b. apply 右并介入...
Qed.

Lemma 函数加点之左应用 : ∀ f a b, 为函数 f → a ∉ dom f → ∀x ∈ dom f, (f ∪ {<a, b>,})[x] = f[x].
Proof. intros. apply 函数应用. apply 函数加点; auto. apply 左并介入. 函数-|. Qed.

Lemma 函数加点之右应用 : ∀ f a b, 为函数 f → a ∉ dom f → (f ∪ {<a, b>,})[a] = b.
Proof. intros. apply 函数应用. apply 函数加点; auto. apply 右并介入; auto. Qed.

Lemma 函数加点之左限制 : ∀ f a b, 为函数 f → a ∉ dom f → (f ∪ {<a, b>,}) ↾ (dom f) = f.
Proof with auto.
  intros f a b Hf 域外. 外延 x Hx.
  - 序偶分离|-Hx. apply 二元并除去 in Hp as []...
    apply 单集除去 in H. apply 序偶相等 in H as []; subst. easy.
  - 函数|-Hx. 序偶分离-|... 域.
Qed.

Lemma 函数加点之右限制 : ∀ f a b, 为函数 f → a ∉ dom f → (f ∪ {<a, b>,}) ↾ {a,} = {<a, b>,}.
Proof with auto.
  intros f a b Hf 域外. 外延 x Hx.
  - 序偶分离|-Hx. apply 二元并除去 in Hp as []...
    apply 单集除去 in Hx; subst. 定 H. easy.
  - apply 单集除去 in Hx; subst. 序偶分离-|...
Qed.

Lemma 函数集族并之定义域 : ∀ F A, dom (⋃ {F x | x ∊ A}) = ⋃ {dom (F x) | x ∊ A}.
Proof with auto.
  intros. 外延 x Hx.
  - 定|-Hx as [y Hp]. apply 集族并除去 in Hp as [a [Ha Hp]].
    apply 集族并介入 with a... 域.
  - apply 集族并除去 in Hx as [a [Ha Hp]]. 定|-Hp as [y Hp].
    定-|y. apply 集族并介入 with a...
Qed.
