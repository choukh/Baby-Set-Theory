(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Replacement.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Function.
Require Import BBST.Lemma.MetaFunction.

Definition 限制 := λ f A, {'<x, y> ∊ f | x ∈ A}.
Notation "f ↾ A" := (限制 f A) (at level 60) : 集合域.

Lemma 限制为函数 : ∀ f A, 为函数 f → 为函数 (f ↾ A).
Proof.
  intros. copy H as [序偶 单值]. split.
  - intros p Hp. 序偶分离|-Hp. auto.
  - intros x y z Hxy Hxz. 序偶分离|-Hxy. 序偶分离|-Hxz.
    函数|-Hp. 函数|-Hp0. auto.
Qed.

Lemma 限制之定义域 : ∀ f A, 为函数 f → A ⊆ dom f → dom (f ↾ A) = A.
Proof with auto.
  intros * 函 子集. 外延.
  - 定|-H as [y H]. 序偶分离|-H...
  - apply 子集 in H as Hp. 定|-Hp as [y Hp]. 定-|y. 序偶分离-|...
Qed.

Lemma 限制之应用 : ∀ f A, 为函数 f → A ⊆ dom f → ∀x ∈ A, (f ↾ A)[x] = f[x].
Proof with auto.
  intros * 函 子集 x Hx. apply 函数应用. apply 限制为函数...
  序偶分离-|... 函数-|. apply 子集...
Qed.

Lemma 限制到父再子 : ∀ f A B, A ⊆ B → (f ↾ B) ↾ A = f ↾ A.
Proof with auto.
  intros. 外延 x Hx.
  - 序偶分离|-Hx. 序偶分离|-Hp. 序偶分离-|...
  - 序偶分离|-Hx. 序偶分离-|... 序偶分离-|...
Qed.

Lemma 限制到子再父 : ∀ f A B, A ⊆ B → (f ↾ A) ↾ B = f ↾ A.
Proof with auto.
  intros. 外延 x Hx.
  - 序偶分离|-Hx.
  - 序偶分离|-Hx. 序偶分离-|... 序偶分离-|...
Qed.

Lemma 替代式限制 : ∀ f A, 为函数 f → A ⊆ dom f → f ↾ A = {<x, f[x]> | x ∊ A}.
Proof with auto.
  intros * Hf 定. 外延 p H.
  - 序偶分离|-H. 函数|-Hp. apply 替代介入. exists a...
  - apply 替代除去 in H as [x [Hx Hp]]. subst.
    序偶分离-|... 函数-|...
Qed.

Definition 类函数限制 := λ F A, 函数 A {F x | x ∊ A} F.
Notation "F ↑ A" := (类函数限制 F A) (at level 60) : 集合域.

Lemma 类函数替代式限制 : ∀ F A, F ↑ A = {<x, F x> | x ∊ A}.
Proof with auto.
  intros. 外延.
  - 关系|-H. subst. apply 替代介入. exists a...
  - apply 替代除去 in H as [a [Ha H]]. subst. 关系-|...
Qed.

Lemma 类函数限制之定义域 : ∀ F A, dom (F ↑ A) = A.
Proof. intros. unfold 类函数限制. rewrite 元定义域; auto. Qed.

Lemma 类函数限制之值域 : ∀ F A, ran (F ↑ A) = {F x | x ∊ A}.
Proof with auto.
  intros. rewrite 类函数替代式限制. 外延 y H.
  - 值|-H as [x H]. apply 替代除去 in H as [x' [Hx' H]].
    apply 序偶相等 in H as []; subst...
  - apply 替代除去 in H as [x [Hx H]]. subst.
    值-|x. apply 替代介入. exists x...
Qed.

Lemma 类函数限制之应用 : ∀ F A, ∀x ∈ A, F x = (F ↑ A)[x].
Proof. intros. apply 函数除去1. apply 函数为之. 关系-|; auto. Qed.
