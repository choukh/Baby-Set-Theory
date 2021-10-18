(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Power.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.BinaryUnion.
Require Import BBST.Definition.Omega.
Require Import BBST.Definition.Function.
Require Import BBST.Lemma.BasicFunction.
Require Import BBST.Lemma.FunctionManeuver.

Section 构造及引理.
Variable f A a : 集合.
Variable Hf: f : A ⇒ A.
Variable Ha: a ∈ A.

Definition 为前段 := λ g,
(* (甲) *) (为函数 g ∧ dom g ⊆ ω ∧ ran g ⊆ A) ∧
(* (乙) *) (∅ ∈ dom g ∧ g[∅] = a) ∧
(* (丙) *) ∀n ∈ ω, n⁺ ∈ dom g → n ∈ dom g ∧ g[n⁺] = f[g[n]].

Notation g₀ := {<∅, a>,}.

Lemma g₀为前段 : 为前段 g₀.
Proof with auto.
  unfold 为前段. rewrite 单点集的定义域, 单点集的值域, 单点函数应用...
  split3; [split3|auto|].
  - apply 单点集为函数.
  - intros x Hx. apply 单集除去 in Hx; subst...
  - intros x Hx. apply 单集除去 in Hx; subst...
  - intros n Hn Hn'. apply 单集除去 in Hn'. exfalso. apply 后继非空 with n...
Qed.
Local Hint Resolve g₀为前段 : core.

Definition 前段集 := {g ∊ 𝒫 (ω × A) | 为前段 g}.

Lemma g₀属于前段集 : g₀ ∈ 前段集.
Proof with auto.
  apply 分离介入... apply 幂集介入. intros p Hp.
  apply 单集除去 in Hp; subst. 直积-|...
Qed.

Definition 前段并 := ⋃ 前段集.

Lemma 核心 : ∀ x y, <x, y> ∈ 前段并 ↔ ∃g ∈ 前段集, 为前段 g ∧ <x, y> ∈ g.
Proof. split.
  - intros 偶. apply 并集除去 in 偶 as [g [Hg 偶]].
    apply 分离之条件 in Hg as 条件. exists g; auto.
  - intros [g [Hg [条件 偶]]]. apply 并集介入 with g; auto.
Qed.

Lemma 零属于前段并的定义域 : ∅ ∈ dom 前段并.
Proof.
  定-|a. apply 核心. exists g₀. split3; auto. apply g₀属于前段集.
Qed.

Lemma 前段并的定义域是ω的子集 : dom 前段并 ⊆ ω.
Proof.
  intros x Hx. 定|-Hx as [y 偶].
  apply 核心 in 偶 as [g [_ [[[_ [定 _]] _] 偶]]]. apply 定. 域.
Qed.

Lemma 前段并的值域是A的子集 : ran 前段并 ⊆ A.
Proof.
  intros y Hy. 值|-Hy as [x 偶].
  apply 核心 in 偶 as [g [_ [[[_ [_ 值]] _] 偶]]]. apply 值. 域.
Qed.

Theorem 前段并为函数 : 为函数 前段并.
Proof with auto. split.
  - (* 前段并为序偶集 *)
    intros p 偶. apply 并集除去 in 偶 as [g [Hg 偶]].
    apply 分离之条件 in Hg as [[函 _] _]. apply 函...
  - (* 前段并满足单值条件 *)
    intros x y z Hxy. assert (x ∈ ω). {
      apply 前段并的定义域是ω的子集. 域.
    }
    generalize dependent Hxy. generalize dependent z. generalize dependent y.
    归纳 x; intros y z Hxy Hxz.
    + (* x = ∅ *)
      apply 核心 in Hxy as [g [_ [[[函g _] [[_ 乙2g] _]] Hxy]]].
      apply 核心 in Hxz as [h [_ [[[函h _] [[_ 乙2h] _]] Hxz]]].
      函数|-Hxy. 函数|-Hxz. rewrite 乙2g, 乙2h...
    + (* x = m⁺ *)
      apply 核心 in Hxy as [g [Hg [前段g Hxy]]].
      apply 核心 in Hxz as [h [Hh [前段h Hxz]]].
      copy 前段g as [[函g _] [_ 丙g]].
      copy 前段h as [[函h _] [_ 丙h]].
      destruct (丙g m) as [丙1g 丙2g]... 域.
      destruct (丙h m) as [丙1h 丙2h]... 域.
      函数|-Hxy. 函数|-Hxz. rewrite 丙2g, 丙2h.
      f_equal. apply 归纳假设.
      * apply 核心. exists g. split... split... 函数-|.
      * apply 核心. exists h. split... split... 函数-|.
Qed.
Local Hint Resolve 前段并为函数 : core.

Theorem 前段并也满足前段条件 : 为前段 前段并.
Proof with auto. split3.
  - (* 甲 *) split3...
    apply 前段并的定义域是ω的子集. apply 前段并的值域是A的子集.
  - (* 乙 *) pose proof 零属于前段并的定义域. split...
    定|-H as [y 偶]. apply 函数应用 in 偶 as 应用...
    apply 核心 in 偶 as [g [_ [[[函 _] [乙 _]] 偶]]].
    函数|-偶. rewrite 应用. apply 乙.
  - (* 丙 *) intros n Hn Hn'. 定|-Hn' as [y' 偶h].
    apply 函数应用 in 偶h as 应用h...
    apply 核心 in 偶h as [g [前段 [条 偶g]]].
    copy 条 as [[函 _] [_ 丙]]. 函数|-偶g... 定 偶g.
    apply 丙 in 偶g as [偶g 归]... 定|-偶g as [y 偶g].
    assert (偶h: <n, y> ∈ 前段并). apply 核心. exists g...
    split. 域. apply 函数应用 in 偶g, 偶h... congruence.
Qed.

Theorem 前段并的定义域为ω : dom 前段并 = ω.
Proof with auto.
  apply 归纳原理. apply 前段并的定义域是ω的子集.
  split. apply 零属于前段并的定义域.
  intros n Hn. 反证. apply 前段并的定义域是ω的子集 in Hn as Hnw...
  set (前段并 ∪ {<n⁺, f[前段并[n]]>,}) as g.
  assert (函: 为函数 g). apply 函数加点...
  assert (定: dom g ⊆ ω). {
    intros x Hx. 函数 Hx... apply 二元并除去 in Hx as [].
    - 定 H. apply 前段并的定义域是ω的子集 in H... 
    - 定 H. rewrite 单点集的定义域 in H. apply 单集除去 in H; subst...
  }
  assert (值: ran g ⊆ A). {
    intros y Hy. 值|-Hy as [x Hp]. apply 二元并除去 in Hp as [].
    - 值 H. apply 前段并的值域是A的子集 in H... 
    - 值 H. rewrite 单点集的值域 in H. apply 单集除去 in H; subst.
      apply 映射除去 with A... apply 前段并的值域是A的子集. 值-|n. 函数-|...
  }
  assert (新前段: 为前段 g). {
    split3... (* 甲 *)
    - (* 乙 *) assert (∅ ∈ dom g). {
        unfold g. rewrite 函数之二元并之定义域... 2: apply 单点集为函数.
        apply 左并介入. apply 零属于前段并的定义域.
      }
      split... 函数 H... apply 二元并除去 in H as [].
      + 函数|-H... apply 前段并也满足前段条件.
      + apply 单集除去 in H. apply 序偶相等 in H as [H _].
        exfalso. apply 后继非空 with n...
    - (* 丙 *) intros k Hk Hk'. unfold g at 1. unfold g in Hk'.
      rewrite 函数之二元并之定义域 in *... 2,3: apply 单点集为函数.
      apply 二元并除去 in Hk' as [].
      + destruct 前段并也满足前段条件 as [_ [_ 丙]].
        apply 丙 in H as H'... destruct H' as [H1 H2]...
        split. apply 左并介入... apply 函数应用, 左并介入... 函数-|...
        rewrite H2. f_equal. apply 函数应用... apply 左并介入. 函数-|...
      + rewrite 单点集的定义域 in H. apply 单集除去 in H.
        apply 后继是单射 in H... subst.
        split. apply 左并介入... apply 函数应用, 右并介入...
        replace (g[n]) with (前段并[n])...
        symmetry. apply 函数应用... apply 左并介入. 函数-|...
  }
  assert (新点: <n⁺, f[前段并[n]]> ∈ g). apply 右并介入...
  assert (旧点: <n⁺, f[前段并[n]]> ∈ 前段并). {
    apply 核心. exists g. split3... apply 分离介入...
    apply 幂集介入. intros p Hp. 函数|-Hp... 直积-|.
    apply 定. 域. apply 值. 域.
  }
  apply 反设. 域.
Qed.

End 构造及引理.

Definition ω递归规范 := λ f A a h,
  h: ω ⇒ A ∧ h[∅] = a ∧ ∀n ∈ ω, h[n⁺] = f[h[n]].

Definition ω递归函数 := λ f A a, 前段并 f A a.

Theorem ω递归定理 : ∀ f A a, f: A ⇒ A → a ∈ A →
  ω递归规范 f A a (ω递归函数 f A a).
Proof with auto.
  intros * Hf Ha. copy Hf as [函 [定 值]]. split3.
  - (* ω递归函数 f A a : ω ⇒ A *) split3.
    apply 前段并为函数. apply 前段并的定义域为ω... apply 前段并的值域是A的子集.
  - (* (ω递归函数 f A a)[∅] = a *)
    apply 前段并也满足前段条件...
  - (* ∀ n : 集合 ∈ ω, (ω递归函数 f A a)[n⁺] = f[(ω递归函数 f A a)[n]] *)
    intros n Hn. destruct (前段并也满足前段条件 f A a) as [_ [_ 丙]]...
    apply 丙... rewrite 前段并的定义域为ω...
Qed.

Fact ω递归函数唯一 : ∀ f A a, f: A ⇒ A → a ∈ A → uniqueness (ω递归规范 f A a).
Proof with auto.
  intros * Hf Ha h1 h2 [[函1 [定1 _]] [H01 H1]] [[函2 [定2 _]] [H02 H2]].
  apply 函数之外延... congruence.
  intros n Hn. rewrite 定1 in Hn. 归纳 n.
  - congruence.
  - apply H1 in Hm as Heq1. apply H2 in Hm as Heq2. congruence.
Qed.
