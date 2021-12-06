(** Coq coding by choukh, Nov 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.
Require Import BBST.Arith.Nat.
Require Import BBST.Arith.Ord.

Local Hint Immediate ω为序数集 : core.
Local Hint Resolve 𝐎𝐍为传递类 一为序数 :core.

Definition 左迭代 := λ α, 序数递归 α (幂运算 α).
Notation "α ^^ᴸ β" := (左迭代 α β) (at level 25) : 序数算术域.

Theorem 左迭代为序数运算 : ∀ α β ⋵ 𝐎𝐍, α ^^ᴸ β ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的递归为序数运算; auto. Qed.
Local Hint Resolve 左迭代为序数运算 : core.

Theorem 左迭代零次 : ∀α ⋵ 𝐎𝐍, α ^^ᴸ 0 = α.
Proof. intros. apply 序数递归_0; auto. Qed.

Theorem 左迭代后继次 : ∀ α β ⋵ 𝐎𝐍, α ^^ᴸ β⁺ = α ^ (α ^^ᴸ β).
Proof. intros. apply 序数递归_后继; auto. Qed.

Theorem 左迭代极限次 : ∀α ⋵ 𝐎𝐍, 极限处连续 (左迭代 α).
Proof. intros. apply 序数递归_极限; auto. Qed.

Lemma 左迭代有限递增 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → 有限递增 (左迭代 α).
Proof with auto.
  intros α Hα H1 n Hn. 归纳 n.
  - rewrite 左迭代后继次, 左迭代零次... apply 幂运算放大...
  - rewrite 左迭代后继次, 左迭代后继次... apply 幂运算保序...
Qed.

Fact 左迭代有限保序 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → 有限保序 (左迭代 α).
Proof with auto.
  intros α Hα H1 n Hn m. 归纳 n; intro Hmn. 空集归谬.
  apply 后继除去 in Hmn as [].
  - apply 序数传递 with (α ^^ᴸ n)... apply 左迭代有限递增...
  - subst. apply 左迭代有限递增...
Qed.

Lemma 左迭代ω次为极限 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → α ^^ᴸ ω ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros α Hα H1. split...
  rewrite 左迭代极限次... 外延.
  - apply 并集除去 in H as [β [Hβ H]].
    apply 集族并除去 in Hβ as [n [Hn Hβ]].
    apply 集族并介入 with n... apply 序数传递 with β...
  - apply 集族并除去 in H as [n [Hn H]].
    apply 并集介入 with (α ^^ᴸ n)...
    apply 集族并介入 with n⁺. apply 极限序数有其任意元素的后继...
    apply 左迭代有限递增...
Qed.

Lemma 左迭代为零 : ∀ α β ⋵ 𝐎𝐍, α ^^ᴸ β = 0 → α = 0.
Proof with eauto.
  intros α Hα. 超限归纳 β Hβ. 超限讨论 β; intros Heq.
  - rewrite 左迭代零次 in Heq...
  - rewrite 左迭代后继次 in Heq... apply 幂为零 in Heq...
  - rewrite 左迭代极限次 in Heq...
    apply 集族并为零 in Heq as []... exfalso...
Qed.

Lemma 左迭代在ω后继处不递增 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → α ^^ᴸ ω⁺ = α ^^ᴸ ω.
Proof with auto.
  intros α Hα H1. rewrite 左迭代后继次, 极限次幂, 左迭代极限次...
  2: apply 左迭代ω次为极限...
  2: { intros H. apply 左迭代为零 in H... apply 大于一的序数不为零 with α... }
  外延.
  - apply 集族并除去 in H as [y [Hy Hx]].
    apply 集族并除去 in Hy as [n [Hn Hy]].
    apply 集族并介入 with n⁺... apply 序数传递 with (α ^ y)...
    rewrite 左迭代后继次... apply 幂运算保序...
  - apply 集族并除去 in H as [n [Hn Hx]].
    apply 集族并介入 with (α ^^ᴸ n).
    apply 集族并介入 with n⁺... apply 左迭代有限递增...
    apply 序数传递 with (α ^^ᴸ n)... rewrite <- 左迭代后继次... apply 左迭代有限递增...
Qed.

Theorem 左迭代在ω之后不变 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → ∀β ⋵ 𝐎𝐍, ω ∈ β → α ^^ᴸ β = α ^^ᴸ ω.
Proof with auto.
  intros α Hα H1. 超限归纳 β; intros H. 超限讨论 β. 空集归谬.
  - apply 后继除去 in H as []...
    + rewrite 左迭代后继次, 归纳假设, <- 左迭代后继次, 左迭代在ω后继处不递增...
    + subst... apply 左迭代在ω后继处不递增...
  - rewrite 左迭代极限次... 外延. 2: apply 集族并介入 with ω...
    apply 集族并除去 in H2 as [γ [Hγ Hx]]. assert (Hγo: γ ⋵ 𝐎𝐍). eauto.
    destruct (序数三歧 γ Hγo ω) as [|[]]... subst... 2: rewrite <- (归纳假设 γ)...
    apply 序数传递 with (α ^^ᴸ γ)... rewrite (左迭代极限次 α Hα ω)...
    apply 集族并介入 with γ⁺... apply 左迭代有限递增...
Qed.

Definition 右迭代 := λ α, 序数递归 α (λ ξ, ξ ^ α).
Notation "α ^^ᴿ β" := (右迭代 α β) (at level 25) : 序数算术域.

Theorem 右迭代为序数运算 : ∀ α β ⋵ 𝐎𝐍, α ^^ᴿ β ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的递归为序数运算; auto. Qed.
Local Hint Resolve 右迭代为序数运算 : core.

Theorem 右迭代零次 : ∀α ⋵ 𝐎𝐍, α ^^ᴿ 0 = α.
Proof. intros. apply 序数递归_0; auto. Qed.

Theorem 右迭代后继次 : ∀ α β ⋵ 𝐎𝐍, α ^^ᴿ β⁺ = (α ^^ᴿ β) ^ α.
Proof. intros. apply 序数递归_后继; auto. Qed.

Theorem 右迭代极限次 : ∀α ⋵ 𝐎𝐍, 极限处连续 (右迭代 α).
Proof. intros. apply 序数递归_极限; auto. Qed.

Lemma 右迭代于一 : ∀α ⋵ 𝐎𝐍, 1 ^^ᴿ α = 1.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 右迭代零次...
  - rewrite 右迭代后继次, 一次幂...
  - rewrite 右迭代极限次... 外延.
    + apply 集族并除去 in H as [β [Hβ H]]. rewrite 归纳假设 in H...
    + simpl in H. apply 后继除去 in H as []... 空集归谬. subst.
      apply 集族并介入 with ∅... rewrite 右迭代零次... simpl...
Qed.

Theorem 右迭代表达式 : ∀ α β ⋵ 𝐎𝐍, α ≠ 0 → α ^^ᴿ β = α ^ (α ^ β).
Proof with auto.
  intros α Hα. 超限归纳 β Hβ. intros Hα0.
  排中 (α = 1) as [|Hα1]. {
    subst. rewrite 右迭代于一, 底数为一的幂...
  }
  超限讨论 β.
  - rewrite 右迭代零次, 零次幂, 一次幂...
  - rewrite 右迭代后继次, 归纳假设, <- 指数积运算律, 后继次幂...
  - rewrite 右迭代极限次, 极限次幂...
    2: apply 幂为极限_右...
    2: intros H; apply 幂为零 in H...
    外延.
    + apply 集族并除去 in H as [γ [Hγ H]]. assert (Hγo: γ ⋵ 𝐎𝐍). eauto.
      apply 集族并介入 with (α ^ γ)... apply 幂运算保序... rewrite <- 归纳假设...
    + apply 集族并除去 in H as [γ [Hγ Hx]]. rewrite 极限次幂 in Hγ...
      apply 集族并除去 in Hγ as [δ [Hδ Hγ]].
      assert (Hγo: γ ⋵ 𝐎𝐍). eauto.
      assert (Hoδ: δ ⋵ 𝐎𝐍). eauto.
      apply 集族并介入 with δ... rewrite 归纳假设...
      apply 序数传递 with (α ^ γ)... apply 幂运算保序...
Qed.

(* α ^ α ^ ... ^ α ^ τ *)
Definition 顶迭代 := λ α β τ, 序数递归 τ (幂运算 α) β.
Notation "α ^^ᵀ β" := (顶迭代 α β) (at level 25) : 序数算术域.

Theorem 顶迭代为序数运算 : ∀ τ α β ⋵ 𝐎𝐍, (α ^^ᵀ β) τ ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的递归为序数运算; auto. Qed.
Local Hint Resolve 顶迭代为序数运算 : core.

Theorem 顶迭代零次 : ∀ τ α ⋵ 𝐎𝐍, (α ^^ᵀ 0) τ = τ.
Proof. intros. apply 序数递归_0; auto. Qed.

Theorem 顶迭代后继次 : ∀ τ α β ⋵ 𝐎𝐍, (α ^^ᵀ β⁺) τ = α ^ (α ^^ᵀ β) τ.
Proof. intros. apply 序数递归_后继; auto. Qed.

Theorem 顶迭代极限次 : ∀ τ α ⋵ 𝐎𝐍, 极限处连续 (λ β, (α ^^ᵀ β) τ).
Proof. intros. apply 序数递归_极限; auto. Qed.

Theorem 顶迭代一次 : ∀ τ α ⋵ 𝐎𝐍, (α ^^ᵀ 1) τ = α ^ τ.
Proof. intros. simpl. rewrite 顶迭代后继次, 顶迭代零次; auto. Qed.

Lemma 顶迭代有限弱递增 : ∀ τ α ⋵ 𝐎𝐍, 1 ∈ α → 有限弱递增 (λ k, (α ^^ᵀ k) τ).
Proof with auto.
  intros τ Hτ α Hα H1 n Hn. 归纳 n.
  - rewrite 顶迭代零次, 顶迭代一次... apply 幂运算弱放大...
  - rewrite 顶迭代后继次, 顶迭代后继次... apply 幂运算保序_弱右...
Qed.

Fact 顶迭代有限弱保序 : ∀ τ α ⋵ 𝐎𝐍, 1 ∈ α → 有限弱保序 (λ k, (α ^^ᵀ k) τ).
Proof with auto.
  intros τ Hτ α Hα H1 n Hn m. 归纳 n; intro Hmn. 空集归谬.
  apply 后继除去 in Hmn as [].
  - apply 序数传递_弱 with ((α ^^ᵀ n) τ)... apply 顶迭代有限弱递增...
  - subst. apply 顶迭代有限弱递增...
Qed.

Lemma 有限顶迭代小于左迭代 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → ∀τ ∈ α, ∀n ∈ ω, (α ^^ᵀ n) τ ∈ α ^^ᴸ n.
Proof with auto.
  intros α Hα H1 τ Hτα n Hn.
  assert (Hτ: τ ⋵ 𝐎𝐍). eauto.
  归纳 n.
  - rewrite 顶迭代零次, 左迭代零次...
  - rewrite 顶迭代后继次, 左迭代后继次... apply 幂运算保序...
Qed.

Lemma 有限左迭代小于后继顶迭代 : ∀α ⋵ 𝐎𝐍, ∀τ ∈ α, 1 ∈ τ → ∀n ∈ ω, α ^^ᴸ n ∈ (α ^^ᵀ n⁺) τ.
Proof with auto.
  intros α Hα τ Hτα H1 n Hn.
  assert (Hτ: τ ⋵ 𝐎𝐍). eauto.
  assert (H1α: 1 ∈ α). apply 序数传递 with τ...
  归纳 n.
  - rewrite 顶迭代一次, 左迭代零次... apply 幂运算放大...
  - rewrite 顶迭代后继次, 左迭代后继次... apply 幂运算保序...
Qed.

Lemma 无限顶迭代等于左迭代 : ∀α ⋵ 𝐎𝐍, ∀τ ∈ α, 1 ∈ τ → (α ^^ᵀ ω) τ = α ^^ᴸ ω.
Proof with auto.
  intros α Hα τ Hτα H1.
  assert (Hτ: τ ⋵ 𝐎𝐍). eauto.
  assert (H1α: 1 ∈ α). apply 序数传递 with τ...
  rewrite 顶迭代极限次, 左迭代极限次...
  外延; apply 集族并除去 in H as [n [Hn H]].
  - apply 集族并介入 with n... apply 序数传递 with ((α ^^ᵀ n) τ)... apply 有限顶迭代小于左迭代...
  - apply 集族并介入 with n⁺... apply 序数传递 with (α ^^ᴸ n)... apply 有限左迭代小于后继顶迭代...
Qed.
