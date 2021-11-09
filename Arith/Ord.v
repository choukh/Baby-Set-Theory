(** Coq coding by choukh, Nov 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.
Require Import BBST.Arith.Nat.

Local Coercion 自动嵌入 := λ n, 嵌入 n.
Local Hint Immediate ω是序数集 : core.
Local Hint Resolve 𝐎𝐍为传递类 : core.

Fact 一为序数 : 1 ⋵ 𝐎𝐍. apply ω是序数集; auto. Qed.
Fact 二为序数 : 2 ⋵ 𝐎𝐍. apply ω是序数集; auto. Qed.
Local Hint Resolve 一为序数 二为序数 : core.

Declare Scope 序数算术域.
Delimit Scope 序数算术域 with ord.
Open Scope 序数算术域.

Definition 加法 := λ α, 序数递归 α 后继.
Notation "α + β" := (加法 α β) : 序数算术域.

Theorem 加法为序数运算 : ∀ α β ⋵ 𝐎𝐍, α + β ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的递归为序数运算; auto. Qed.
Global Hint Resolve 加法为序数运算 : core.

Theorem 加零 : ∀α ⋵ 𝐎𝐍, α + 0 = α.
Proof. intros. apply 序数递归_0. Qed.

Theorem 加后继 : ∀ α β ⋵ 𝐎𝐍, α + β⁺ = (α + β)⁺.
Proof. intros. apply 序数递归_后继; auto. Qed.

Corollary 加一 : ∀α ⋵ 𝐎𝐍, α + 1 = α⁺.
Proof. intros. simpl. rewrite 加后继, 加零; auto. Qed.

Theorem 加极限 : ∀α ⋵ 𝐎𝐍, 极限处连续 (加法 α).
Proof. intros. apply 序数递归_极限. Qed.

Theorem 加法等效 : ∀ n m ∈ ω, n + m = (n + m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 加零, Nat.加零...
  - rewrite 加后继, Nat.加后继, 归纳假设...
Qed.

Corollary 加法对ω封闭 : ∀ m n ∈ ω, m + n ∈ ω.
Proof. intros m Hm n Hn. rewrite 加法等效; auto. Qed.

Corollary 有限加于一 : ∀α ∈ ω, 1 + α = α⁺.
Proof. intros. rewrite 加法等效, 加于一; auto. Qed.

Example 一加一等于二 : 1 + 1 = 2.
Proof. rewrite 有限加于一; auto. Qed.

Example 一加ω等于ω : 1 + ω = ω.
Proof with auto.
  rewrite 加极限... 外延 α Hα.
  - apply 集族并除去 in Hα as [β [Hβ Hα]].
    apply ω为传递集 with (1 + β)... apply 加法对ω封闭...
  - apply 集族并介入 with α... rewrite 加法等效, 加于一...
Qed.

Example ω加一等于ω的后继 : ω + 1 = ω⁺.
Proof. simpl. rewrite 加后继, 加零; auto. Qed.

Theorem 加于零 : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - apply 加零...
  - rewrite 加后继, 归纳假设...
  - rewrite 加极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]].
      rewrite 归纳假设 in Hξ... apply 序数传递 with β...
    + apply 极限序数有其任意元素的后继 in Hξ...
      apply 集族并介入 with ξ⁺... rewrite 归纳假设...
Qed.

Theorem 无限加于一 : ∀α ⋵ 𝐎𝐍, ω ⋸ α → 1 + α = α.
Proof with auto.
  超限归纳. intros Hle.
  destruct Hle. 2: subst; apply 一加ω等于ω. 超限讨论 α.
  - 空集归谬.
  - rewrite 加后继, 归纳假设... apply 小于等于即小于后继...
  - rewrite 加极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. 排中 (β ∈ ω).
      * apply 序数传递 with β⁺... rewrite <- 有限加于一...
        apply 极限序数有其任意元素的后继...
      * rewrite 归纳假设 in Hξ... apply 序数传递 with β...
        反证. apply 序数可换 in 反设... eauto.
    + 排中 (ξ ∈ ω).
      * apply 集族并介入 with ξ... rewrite 有限加于一...
      * apply 集族并介入 with ξ⁺... apply 极限序数有其任意元素的后继...
        rewrite 加后继, 归纳假设... 反证. apply 序数可换 in 反设... eauto. eauto.
Qed.

Definition 乘法 := λ α, 序数递归 0 (λ ξ, ξ + α).
Notation "α * β" := (乘法 α β) : 序数算术域.

Theorem 乘法为序数运算 : ∀ α β ⋵ 𝐎𝐍, α * β ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的递归为序数运算; auto. Qed.
Global Hint Resolve 乘法为序数运算 : core.

Theorem 乘零 : ∀α ⋵ 𝐎𝐍, α * 0 = 0.
Proof. intros. apply 序数递归_0. Qed.

Theorem 乘后继 : ∀ α β ⋵ 𝐎𝐍, α * β⁺ = α * β + α.
Proof. intros. apply 序数递归_后继; auto. Qed.

Corollary 乘一 : ∀α ⋵ 𝐎𝐍, α * 1 = α.
Proof. intros. simpl. rewrite 乘后继, 乘零, 加于零; auto. Qed.

Theorem 乘极限 : ∀α ⋵ 𝐎𝐍, 极限处连续 (乘法 α).
Proof. intros. apply 序数递归_极限. Qed.

Theorem 乘法等效 : ∀ n m ∈ ω, n * m = (n * m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 乘零, Nat.乘零...
  - rewrite 乘后继, Nat.乘后继, 归纳假设, 加法交换律, 加法等效...
Qed.

Corollary 乘法对ω封闭 : ∀ m n ∈ ω, m * n ∈ ω.
Proof. intros m Hm n Hn. rewrite 乘法等效; auto. Qed.

Theorem 乘于零 : ∀α ⋵ 𝐎𝐍, 0 * α = 0.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 乘零...
  - rewrite 乘后继, 加零, 归纳假设...
  - rewrite 乘极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. rewrite 归纳假设 in Hξ...
    + simpl in Hξ. 空集归谬.
Qed.

Theorem 乘于一 : ∀α ⋵ 𝐎𝐍, 1 * α = α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - apply 乘零...
  - rewrite 乘后继, 归纳假设, 加一...
  - rewrite 乘极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]].
      rewrite 归纳假设 in Hξ... apply 序数传递 with β...
    + apply 极限序数有其任意元素的后继 in Hξ...
      apply 集族并介入 with ξ⁺... rewrite 归纳假设...
Qed.

Definition 幂运算 := λ α, 缺零递归 1 (λ ξ, ξ * α).
Notation "α ^ β" := (幂运算 α β): 序数算术域.

Theorem 幂运算为序数运算 : ∀ α β ⋵ 𝐎𝐍, α ^ β ⋵ 𝐎𝐍.
Proof. intros. apply 序数运算的缺零递归为序数运算; auto. Qed.
Global Hint Resolve 幂运算为序数运算 : core.

Theorem 零次幂 : ∀α ⋵ 𝐎𝐍, α ^ 0 = 1.
Proof. intros. apply 缺零递归_0. Qed.

Theorem 后继次幂 : ∀ α β ⋵ 𝐎𝐍, α ^ β⁺ = α ^ β * α.
Proof. intros. apply 缺零递归_后继; auto. Qed.

Corollary 一次幂 : ∀α ⋵ 𝐎𝐍, α ^ 1 = α.
Proof. intros. simpl. rewrite 后继次幂, 零次幂, 乘于一; auto. Qed.

Theorem 极限次幂 : ∀α ⋵ 𝐎𝐍, α ≠ ∅ → 极限处连续 (幂运算 α).
Proof with auto.
  intros α Hα Hα0 γ Hγ Hγ0. unfold 幂运算 at 1.
  rewrite 缺零递归_极限... fold (幂运算 α). 外延.
  - apply 集族并除去 in H as [δ [Hδ Hx]]. apply 分离之父集 in Hδ.
    apply 集族并介入 with δ...
  - apply 集族并除去 in H as [δ [Hδ Hx]]. 排中 (δ = 0).
    + subst. rewrite 零次幂 in Hx... apply 集族并介入 with 1.
      * apply 分离介入. apply 极限序数有其任意元素的后继... apply 单集外介入. simpl...
      * rewrite 一次幂... simpl in Hx. apply 后继除去 in Hx as []. 空集归谬. subst...
    + apply 集族并介入 with δ... apply 分离介入... apply 单集外介入...
Qed.

Theorem 幂运算等效 : ∀ n m ∈ ω, n ^ m = (n ^ m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 零次幂, Nat.零次幂...
  - rewrite 后继次幂, Nat.后继次幂, 归纳假设, 乘法交换律, 乘法等效...
Qed.

Corollary 幂运算对ω封闭 : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof. intros m Hm n Hn. rewrite 幂运算等效; auto. Qed.

Theorem 底数为零的幂 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 0 ^ α = 0.
Proof with auto.
  超限归纳. intros H0. 超限讨论 α.
  - exfalso...
  - rewrite 后继次幂, 乘零...
  - unfold 幂运算. rewrite 缺零递归_极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]].
      apply 分离除去 in Hβ as [Hβ Hβ']. apply 单集外除去 in Hβ'.
      fold (幂运算 0) in Hξ. rewrite 归纳假设 in Hξ...
    + simpl in Hξ. 空集归谬.
Qed.

Theorem 底数为一的幂 : ∀α ⋵ 𝐎𝐍, 1 ^ α = 1.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 零次幂...
  - rewrite 后继次幂, 乘一, 归纳假设...
  - rewrite 极限次幂... 2: simpl... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. rewrite 归纳假设 in Hξ...
    + simpl in Hξ. apply 后继除去 in Hξ as []. 空集归谬. subst.
      apply 集族并介入 with 0... rewrite 零次幂... simpl...
Qed.
