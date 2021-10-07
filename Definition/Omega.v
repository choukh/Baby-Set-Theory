(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Axiom.Union.
Require Import BBST.Axiom.Infinity.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.OneTwo.
Require Import BBST.Definition.Successor.
Require Import BBST.Definition.TransitiveSet.

Definition 为自然数 := λ n, ∀ A, 归纳的 A → n ∈ A.

Definition ω := {a ∊ 𝐈 | 为自然数 a}.

Theorem ω是任意归纳集的共通部分 : ∀ A, 归纳的 A → ω ⊆ A.
Proof. intros. apply 分离之条件 in H0. auto. Qed.

Theorem ω里有且仅有自然数 : ∀ n, n ∈ ω ↔ 为自然数 n.
Proof.
  split.
  - intros n属于ω. now apply 分离除去 in n属于ω.
  - intros n为自然数. apply 分离介入; auto.
    apply n为自然数. apply 无穷公理.
Qed.

(* 皮亚诺公理1 *)
Lemma 零是自然数 : ∅ ∈ ω.
Proof.
  apply 分离介入. apply 无穷公理. intros A [H _]. auto.
Qed.

Lemma ω不为零 : ω ≠ ∅.
Proof.
  intros H. pose proof 零是自然数.
  rewrite H in H0. 空集归谬.
Qed.

Global Hint Immediate 零是自然数 ω不为零 : core.

(* 皮亚诺公理2 *)
Theorem ω是归纳集 : 归纳的 ω.
Proof.
  split. auto.
  intros a Ha. apply 分离之条件 in Ha. apply 分离介入.
  - apply 无穷公理. apply Ha. apply 无穷公理.
  - intros A A归纳. apply A归纳. apply Ha. apply A归纳.
Qed.

Corollary ω归纳 : ∀n ∈ ω, n⁺ ∈ ω.
Proof. apply ω是归纳集. Qed.
Global Hint Resolve ω归纳 : core.

Fact 壹是自然数 : 壹 ∈ ω.
Proof. rewrite <- 零的后继为壹. auto. Qed.
Global Hint Immediate 壹是自然数 : core.

Fact 贰是自然数 : 贰 ∈ ω.
Proof. rewrite <- 壹的后继为贰. auto. Qed.
Global Hint Immediate 贰是自然数 : core.

(* 皮亚诺公理3 *)
Theorem 零不是任何自然数的后继 : ¬ ∃ n ∈ ω, n⁺ = ∅.
Proof. intros [n [Hn H]]. eapply 后继非空. apply H. Qed.

(* 皮亚诺公理5 *)
Theorem 归纳原理 : ∀ N, N ⊆ ω → 归纳的 N → N = ω.
Proof.
  intros N N子集 N归纳. 外延 n Hn.
  - apply N子集. apply Hn.
  - apply 分离之条件 in Hn. apply Hn. apply N归纳.
Qed.

Ltac 归纳 n :=
  pattern n;
  match goal with | H : n ∈ ω |- ?G _ =>
  let N := fresh "N" in
  set {n ∊ ω | G n} as N; simpl in N;
  cut (N = ω); [
    intros ?Heq; rewrite <- Heq in H;
    apply 分离除去 in H as []; auto|
    apply 归纳原理; [
      intros ?x ?Hx; apply 分离除去 in Hx as []; auto|
      split; [apply 分离介入; [apply 零是自然数|]|]
    ]; [|
      let m := fresh "m" in let Hm := fresh "Hm" in
      intros m Hm; apply 分离除去 in Hm as [Hm ?归纳假设];
      apply 分离介入; [apply ω归纳; auto|]
    ]
  ]; clear N; simpl
end.

Theorem 非零自然数的前驱存在 : ∀n ∈ ω, n ≠ ∅ → ∃k ∈ ω, n = k⁺.
Proof.
  intros n Hn. 归纳 n.
  - (* n = ∅ *) intros 矛盾. easy.
  - (* n = m⁺ *) intros _. exists m. split; easy.
Qed.

Ltac 讨论 n := match goal with | Hn: n ∈ ω |- _ =>
  let H := fresh "H" in let p := fresh "p" in
  let Hp := fresh "Hp" in let Heq := fresh "Heq" in
  排中 (n = ∅) as [|H]; [|
    apply (非零自然数的前驱存在 n Hn) in H as [p [Hp Heq]]
  ]; subst n; [|rename p into n] end.

(* 练习5-1 *)
Fact 零小于后继数 : ∀n ∈ ω, ∅ ∈ n⁺.
Proof. intros n Hn. 归纳 n; auto. Qed.
Global Hint Immediate 零小于后继数 : core.

Theorem ω是传递集 : 为传递集 ω.
Proof.
  apply 传递集即其元素都为其子集.
  intros n Hn. 归纳 n.
  - (* n = ∅ *) auto.
  - (* n = m⁺ *) intros x Hx. apply 后继除去 in Hx as [].
    + now apply 归纳假设.
    + now subst.
Qed.
Global Hint Immediate ω是传递集 : core.

Theorem 自然数是传递集 : ∀n ∈ ω, 为传递集 n.
Proof with eauto.
  intros n Hn. 归纳 n; intros p q Hp Hq.
  - 空集归谬.
  - apply 后继除去 in Hq as [].
    + apply 左后继介入. eapply 归纳假设; eauto.
    + subst. auto.
Qed.
Global Hint Immediate 自然数是传递集 : core.

(* 皮亚诺公理4 *)
Lemma 后继是单射 : ∀ n m ∈ ω, n⁺ = m⁺ → n = m.
Proof.
  intros n Hn m Hm 相等.
  apply 自然数是传递集 in Hn, Hm.
  rewrite 传递集即其后继的并等于自身 in Hn, Hm.
  congruence.
Qed.
