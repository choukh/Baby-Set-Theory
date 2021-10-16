(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.BinaryIntersect.
Require Import BBST.Definition.Function.
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
