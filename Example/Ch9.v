(** Coq coding by choukh, Sep 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Pairing.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.OrderedPair.
Require Import BBST.Definition.Product.

Module 错误的序偶.

Definition 序偶 := λ a b, {a, {b,}}.

Fact 有歧义 : 序偶 {∅,} {∅,} = 序偶 {{∅,},} ∅.
Proof. unfold 序偶. apply 配对与顺序无关. Qed.

End 错误的序偶.

Fact 序偶的递归定义 : ∀ a b c, <a, b, c> = <<a, b>, c>.
Proof. reflexivity. Qed.

Example 序偶化简 : ∀ a b, 右 <a, 左 <a, b>> = a.
Proof. intros a b. 化简. Qed.

Example 测试_序偶分离介入1 : {'<x, y> ∊ {<∅, ∅>, <∅, {∅,}>} | x = y} = {<∅, ∅>,}.
Proof with auto.
  intros. 外延.
  - 序偶分离|-H. apply 配对除去 in Hp as [].
    + apply 序偶相等 in H0 as []; subst...
    + apply 序偶相等 in H0 as []; subst.
      exfalso. apply 非空除去 with ∅... exists ∅. rewrite H at 2...
  - 序偶分离-|∅ ∅. now apply 单集除去 in H.
Qed.

Example 测试_序偶分离介入2 : <∅, ∅> ∈ {'<x, y> ∊ {<∅, ∅>, <∅, {∅,}>} | x = y}.
Proof. 序偶分离-|; auto. Qed.

(* 练习9-1 *)
Fact 直积是单射: ∀ A B C, 非空 A → A × B = A × C → B = C.
Proof with auto.
Admitted.
