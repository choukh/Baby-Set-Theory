(** Coq coding by choukh, Nov 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.
Require Import BBST.Arith.Nat.

Local Hint Immediate ω为序数集 : core.
Local Hint Resolve 𝐎𝐍为传递类 : core.

Fact 一为序数 : 1 ⋵ 𝐎𝐍. apply ω为序数集; auto. Qed.
Fact 二为序数 : 2 ⋵ 𝐎𝐍. apply ω为序数集; auto. Qed.
Global Hint Resolve 一为序数 二为序数 : core.

Fact 零不为一 : 嵌入 0 ≠ 嵌入 1.
Proof. intros H. apply 后继非空 with 0. auto. Qed.
Global Hint Immediate 零不为一 : core.

Fact 不为零和一的序数大于一 : ∀ α ⋵ 𝐎𝐍, α ≠ 0 → α ≠ 1 → 1 ∈ α.
Proof with auto.
  intros α Hα H0 H1. 反证.
  destruct (序数三歧 α Hα 1) as [|[]]...
  apply 后继除去 in H as []. 空集归谬. subst...
Qed.

Fact 大于一的序数不为零 : ∀ α ⋵ 𝐎𝐍, 1 ∈ α → α ≠ 0.
Proof. intros α Hα H1 H. subst. simpl in H1. 空集归谬. Qed.

Fact 大于一的序数不为一 : ∀ α ⋵ 𝐎𝐍, 1 ∈ α → α ≠ 1.
Proof. intros α Hα H1 H. subst. apply 序数反自反 with 1; auto. Qed.
Global Hint Resolve 不为零和一的序数大于一 大于一的序数不为零 大于一的序数不为一 : core.

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
Proof. intros α Hα. apply 序数递归_极限. Qed.

Theorem 有限加法等效 : ∀ n m ∈ ω, n + m = (n + m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 加零, Nat.加零...
  - rewrite 加后继, Nat.加后继, 归纳假设...
Qed.

Corollary 加法对ω封闭 : ∀ m n ∈ ω, m + n ∈ ω.
Proof. intros m Hm n Hn. rewrite 有限加法等效; auto. Qed.

Corollary 有限加于一 : ∀n ∈ ω, 1 + n = n⁺.
Proof. intros. rewrite 有限加法等效, 加于一; auto. Qed.

Example 一加一等于二 : 1 + 1 = 2.
Proof. rewrite 有限加于一; auto. Qed.

Example 一加ω等于ω : 1 + ω = ω.
Proof with auto.
  rewrite 加极限... rewrite (替代改写 有限加于一). 外延 α Hα.
  - apply 集族并除去 in Hα as [β [Hβ Hα]]. apply ω为传递集 with β⁺...
  - apply 集族并介入 with α...
Qed.

Example ω加一等于ω的后继 : ω + 1 = ω⁺.
Proof. simpl. rewrite 加一; auto. Qed.

Theorem 加于零 : ∀α ⋵ 𝐎𝐍, 0 + α = α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - apply 加零...
  - rewrite 加后继, 归纳假设...
  - rewrite 加极限, (替代改写 归纳假设)... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. apply 序数传递 with β...
    + apply 集族并介入 with ξ⁺... apply 极限序数有其任意元素的后继...
Qed.

Theorem 无限加于一 : ∀α ⋵ 𝐎𝐍, ω ⋸ α → 1 + α = α.
Proof with auto.
  超限归纳. intros Hle.
  destruct Hle. 2: subst; apply 一加ω等于ω. 超限讨论 α.
  - 空集归谬.
  - rewrite 加后继, 归纳假设... apply 小于等于即小于后继...
  - rewrite 加极限... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. 排中 (ω ⋸ β).
      * rewrite 归纳假设 in Hξ... apply 序数传递 with β...
      * apply 序数传递 with β⁺... rewrite <- 有限加于一...
        apply 序数可换... eauto. apply 极限序数有其任意元素的后继...
    + 排中 (ω ⋸ ξ).
      * apply 集族并介入 with ξ⁺. apply 极限序数有其任意元素的后继...
        rewrite 加后继, 归纳假设... eauto.
      * apply 集族并介入 with ξ... rewrite 有限加于一... apply 序数可换... eauto.
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

Corollary 乘二 : ∀α ⋵ 𝐎𝐍, α * 2 = α + α.
Proof. intros. simpl. rewrite 乘后继, 乘一; auto. Qed.

Theorem 乘极限 : ∀α ⋵ 𝐎𝐍, 极限处连续 (乘法 α).
Proof. intros α Hα. apply 序数递归_极限. Qed.

Theorem 有限乘法等效 : ∀ n m ∈ ω, n * m = (n * m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 乘零, Nat.乘零...
  - rewrite 乘后继, Nat.乘后继, 归纳假设, 加法交换律, 有限加法等效...
Qed.

Corollary 乘法对ω封闭 : ∀ m n ∈ ω, m * n ∈ ω.
Proof. intros m Hm n Hn. rewrite 有限乘法等效; auto. Qed.

Theorem 乘于零 : ∀α ⋵ 𝐎𝐍, 0 * α = 0.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 乘零...
  - rewrite 乘后继, 加零, 归纳假设...
  - rewrite 乘极限, (替代改写 归纳假设)... simpl. 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. 空集归谬.
    + 空集归谬.
Qed.

Theorem 乘于一 : ∀α ⋵ 𝐎𝐍, 1 * α = α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - apply 乘零...
  - rewrite 乘后继, 归纳假设, 加一...
  - rewrite 乘极限, (替代改写 归纳假设)... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. apply 序数传递 with β...
    + apply 集族并介入 with ξ⁺... apply 极限序数有其任意元素的后继...
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
      * rewrite 一次幂... apply 后继除去 in Hx as []. 空集归谬. subst...
    + apply 集族并介入 with δ... apply 分离介入... apply 单集外介入...
Qed.

Theorem 有限幂运算等效 : ∀ n m ∈ ω, n ^ m = (n ^ m)%ω.
Proof with auto.
  intros n Hn. 归纳 m.
  - rewrite 零次幂, Nat.零次幂...
  - rewrite 后继次幂, Nat.后继次幂, 归纳假设, 乘法交换律, 有限乘法等效...
Qed.

Corollary 幂运算对ω封闭 : ∀ m n ∈ ω, m ^ n ∈ ω.
Proof. intros m Hm n Hn. rewrite 有限幂运算等效; auto. Qed.

Theorem 底数为零的幂 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 0 ^ α = 0.
Proof with auto.
  超限归纳. intros H0. 超限讨论 α.
  - exfalso...
  - rewrite 后继次幂, 乘零...
  - unfold 幂运算. rewrite 缺零递归_极限... fold (幂运算 0). 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [β [Hβ Hξ]]. apply 分离除去 in Hβ as [Hβ Hβ'].
      apply 单集外除去 in Hβ'. rewrite 归纳假设 in Hξ...
    + simpl in Hξ. 空集归谬.
Qed.

Theorem 底数为一的幂 : ∀α ⋵ 𝐎𝐍, 1 ^ α = 1.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 零次幂...
  - rewrite 后继次幂, 乘一, 归纳假设...
  - rewrite 极限次幂, (替代改写 归纳假设)... 2: simpl... 外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [_ [_ Hξ]]...
    + apply 后继除去 in Hξ as []. 空集归谬. subst.
      apply 集族并介入 with 0... simpl...
Qed.

(** 序数嵌入 **)

Lemma 和为零 : ∀ α β ⋵ 𝐎𝐍, α + β = 0 → α = 0 ∧ β = 0.
Proof with auto.
  intros α Hα β Hβ H0. 超限讨论 α; 超限讨论 β; subst...
  - rewrite 加于零 in H0...
  - rewrite 加于零 in H0...
  - rewrite 加零 in H0...
  - rewrite 加后继 in H0... exfalso. apply 后继非空 with (α⁺ + β)...
  - exfalso. rewrite 加极限 in H0... apply 集族并为零 in H0 as []...
    apply 后继非空 with α... rewrite <- (H0 ∅), 加零... 
  - rewrite 加零 in H0...
  - rewrite 加后继 in H0... exfalso. apply 后继非空 with (α + β)...
  - exfalso. rewrite 加极限 in H0... apply 集族并为零 in H0 as []...
    apply H1. rewrite <- (H ∅), 加零...
Qed.

Lemma 积为零 : ∀ α β ⋵ 𝐎𝐍, α * β = 0 → α = 0 ∨ β = 0.
Proof with auto.
  intros α Hα. 超限归纳 β Hβ. intros H0. 超限讨论 β...
  - rewrite 乘后继 in H0... apply 和为零 in H0 as []...
  - rewrite 乘极限 in H0... apply 集族并为零 in H0 as []...
    apply 非空介入 in H1 as [γ Hγ].
    apply 极限序数有其任意元素的后继 in Hγ...
    apply 归纳假设 in Hγ as []... exfalso. apply 后继非空 with γ...
Qed.

Lemma 幂为零 : ∀ α β ⋵ 𝐎𝐍, α ^ β = 0 → α = 0.
Proof with auto.
  intros α Hα. 超限归纳 β Hβ. intros H0. 超限讨论 β.
  - rewrite 零次幂 in H0... simpl in H0. exfalso. apply 后继非空 with ∅...
  - rewrite 后继次幂 in H0...
    apply 积为零 in H0 as []... apply 归纳假设 with β...
  - 反证. rewrite 极限次幂 in H0... apply 集族并为零 in H0 as []...
    apply 反设. simpl. rewrite <- (H 1), 一次幂...
    apply 极限序数有其任意元素的后继...
Qed.

Lemma 加法递增 : ∀α ⋵ 𝐎𝐍, 后继处递增 (加法 α).
Proof. intros. rewrite 加后继; auto. Qed.

Theorem 加法为序数嵌入 : ∀α ⋵ 𝐎𝐍, 为序数嵌入 (加法 α).
Proof with auto. intros. split3... apply 加法递增... apply 加极限... Qed.

Corollary 加法保序 : ∀α ⋵ 𝐎𝐍, 保序 (加法 α).
Proof. intros. apply 序数嵌入保序, 加法为序数嵌入; auto. Qed.

Corollary 加法双向保序 : ∀ α β γ ⋵ 𝐎𝐍, β ∈ γ ↔ α + β ∈ α + γ.
Proof with auto. intros. apply 保序运算双向保序... apply 加法保序... Qed.

Lemma 乘法递增 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 后继处递增 (乘法 α).
Proof with auto. intros. rewrite 乘后继, <- 加零 at 1... apply 加法保序... Qed.

Theorem 乘法为序数嵌入 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 为序数嵌入 (乘法 α).
Proof with auto. intros. split3... apply 乘法递增... apply 乘极限... Qed.

Corollary 乘法保序 : ∀α ⋵ 𝐎𝐍, α ≠ 0 → 保序 (乘法 α).
Proof. intros. apply 序数嵌入保序, 乘法为序数嵌入; auto. Qed.

Corollary 乘法双向保序 : ∀ α β γ ⋵ 𝐎𝐍, α ≠ 0 → β ∈ γ ↔ α * β ∈ α * γ.
Proof with auto. intros. apply 保序运算双向保序... apply 乘法保序... Qed.

Lemma 幂运算递增 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → 后继处递增 (幂运算 α).
Proof with auto.
  intros α Hα H1 β Hβ. rewrite 后继次幂... rewrite <- 乘一 at 1...
  apply 乘法保序... intros H. apply 幂为零 in H... subst. simpl in H1. 空集归谬.
Qed.

Theorem 幂运算为序数嵌入 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → 为序数嵌入 (幂运算 α).
Proof with auto. intros. split3... apply 幂运算递增... apply 极限次幂... Qed.

Corollary 幂运算保序 : ∀α ⋵ 𝐎𝐍, 1 ∈ α → 保序 (幂运算 α).
Proof. intros. apply 序数嵌入保序, 幂运算为序数嵌入; auto. Qed.

Corollary 幂运算双向保序 : ∀ α β γ ⋵ 𝐎𝐍, 1 ∈ α → β ∈ γ ↔ α ^ β ∈ α ^ γ.
Proof with auto. intros. apply 保序运算双向保序... apply 幂运算保序... Qed.

Corollary 和为极限 : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐋𝐈𝐌, β ≠ 0 → α + β ⋵ 𝐋𝐈𝐌.
Proof with auto. intros. apply 序数嵌入在极限处的值为极限... apply 加法为序数嵌入... Qed.

Corollary 积为极限_右 : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐋𝐈𝐌, α ≠ 0 → β ≠ 0 → α * β ⋵ 𝐋𝐈𝐌.
Proof with auto. intros. apply 序数嵌入在极限处的值为极限... apply 乘法为序数嵌入... Qed.

Corollary 幂为极限_右 : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐋𝐈𝐌, 1 ∈ α → β ≠ 0 → α ^ β ⋵ 𝐋𝐈𝐌.
Proof with auto. intros. apply 序数嵌入在极限处的值为极限... apply 幂运算为序数嵌入... Qed.

Corollary 积为极限_左 : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐋𝐈𝐌, β * α ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros. 排中 (β = 0). subst. rewrite 乘于零...
  copy H0 as [Hβ _]. 超限讨论 α.
  - rewrite 乘零... apply 零为极限.
  - rewrite 乘后继... apply 和为极限...
  - apply 积为极限_右...
Qed.

Corollary 幂为极限_左 : ∀α ⋵ 𝐎𝐍, ∀β ⋵ 𝐋𝐈𝐌, α ≠ 0 → β ^ α ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros. 排中 (β = 0). subst. rewrite 底数为零的幂...
  copy H0 as [Hβ _]. 超限讨论 α. exfalso...
  - rewrite 后继次幂... apply 积为极限_右... intros H'. apply 幂为零 in H'...
  - apply 幂为极限_右... apply 极限序数有其任意元素的后继...
Qed.

(** 运算律 **)

Theorem 加法结合律 : ∀ α β γ ⋵ 𝐎𝐍, α + β + γ = α + (β + γ).
Proof with auto.
  intros α Hα β Hβ. 超限归纳 γ Hγ. 超限讨论 γ.
  - repeat rewrite 加零...
  - repeat rewrite 加后继... rewrite 归纳假设...
  - rewrite 加极限, (加极限 α Hα (β + γ)), (替代改写 归纳假设)...
    2: apply 和为极限... 2: intros H; apply 和为零 in H as []...
    外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [δ [Hδ Hξ]].
      apply 集族并介入 with (β + δ)... apply 加法保序...
    + apply 集族并除去 in Hξ as [δ [Hδ Hξ]]. rewrite 加极限 in Hδ...
      apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hεo: ε ⋵ 𝐎𝐍) by eauto. assert (Hδo: δ ⋵ 𝐎𝐍) by eauto.
      apply 集族并介入 with ε... apply 序数传递 with (α + δ)... apply 加法保序...
Qed.

Theorem 乘法分配律 : ∀ α β γ ⋵ 𝐎𝐍, α * (β + γ) = α * β + α * γ.
Proof with auto.
  intros α Hα β Hβ. 超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 加零, 乘零, 加零...
  - rewrite 乘后继, 加后继, 乘后继, 归纳假设, 加法结合律...
  - 排中 (α = 0) as [|Hα0]. subst. repeat rewrite 乘于零... rewrite 加零...
    外延 ξ Hξ.
    + rewrite 乘极限 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]].
      2: apply 和为极限... 2: intros H; apply 和为零 in H as []...
      rewrite 加极限 in Hδ... apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 序数传递 with (α * δ), 序数传递 with (α * (β + ε))...
      apply 乘法保序... rewrite 归纳假设... apply 加法保序, 乘法保序...
    + rewrite 加极限 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]].
      2: apply 积为极限_右... 2: intros H; apply 积为零 in H as []...
      rewrite 乘极限 in Hδ... apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 序数传递 with (α * β + δ), 序数传递 with (α * β + α * ε)...
      apply 加法保序... rewrite <- 归纳假设... apply 乘法保序, 加法保序...
Qed.

Theorem 乘法结合律 : ∀ α β γ ⋵ 𝐎𝐍, α * β * γ = α * (β * γ).
Proof with auto.
  intros α Hα β Hβ. 超限归纳 γ Hγ. 超限讨论 γ.
  - repeat rewrite 乘零...
  - repeat rewrite 乘后继... rewrite 归纳假设... rewrite 乘法分配律...
  - 排中 (α = 0) as [|Hα0]. subst. repeat rewrite 乘于零...
    排中 (β = 0) as [|Hβ0]. subst. rewrite 乘于零, 乘零, 乘于零...
    rewrite 乘极限, (乘极限 α Hα (β * γ)), (替代改写 归纳假设)...
    2: apply 积为极限_右... 2: intros H; apply 积为零 in H as []...
    外延 ξ Hξ.
    + apply 集族并除去 in Hξ as [δ [Hδ Hξ]]. assert (Hδo: δ ⋵ 𝐎𝐍) by eauto.
      apply 集族并介入 with (β * δ)... apply 乘法保序...
    + apply 集族并除去 in Hξ as [δ [Hδ Hξ]]. rewrite 乘极限 in Hδ...
      apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 集族并介入 with ε... apply 序数传递 with (α * δ)... apply 乘法保序...
Qed.

Theorem 指数和运算律 : ∀ α β γ ⋵ 𝐎𝐍, α ^ (β + γ) = α ^ β * α ^ γ.
Proof with auto.
  intros α Hα β Hβ. 超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 加零, 零次幂, 乘一...
  - rewrite 加后继, 后继次幂, 后继次幂, 归纳假设, 乘法结合律...
  - assert (和不为零: β + γ ≠ 0). intros H. apply 和为零 in H as []...
    排中 (β = 0) as [|Hβ0]. subst. rewrite 加于零, 零次幂, 乘于一...
    排中 (α = 0) as [|Hα0]. subst. repeat rewrite 底数为零的幂... rewrite 乘零...
    排中 (α = 1) as [|Hα1]. subst. repeat rewrite 底数为一的幂... rewrite 乘一...
    assert (幂不为零: α ^ β ≠ 0). intros H. apply 幂为零 in H...
    外延 ξ Hξ.
    + rewrite 极限次幂 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]]. 2: apply 和为极限...
      rewrite 加极限 in Hδ... apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 序数传递 with (α ^ δ), 序数传递 with (α ^ (β + ε))...
      apply 幂运算保序... rewrite 归纳假设... apply 乘法保序, 幂运算保序...
    + rewrite 乘极限 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]].
      2: apply 幂为极限_右... 2: intros H; apply 幂为零 in H...
      rewrite 极限次幂 in Hδ... apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 序数传递 with (α ^ β * δ), 序数传递 with (α ^ β * α ^ ε)...
      apply 乘法保序... rewrite <- 归纳假设... apply 幂运算保序, 加法保序...
Qed.

Theorem 指数积运算律 : ∀ α β γ ⋵ 𝐎𝐍, α ^ (β * γ) = (α ^ β) ^ γ.
Proof with auto.
  intros α Hα β Hβ. 超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 零次幂, 乘零, 零次幂...
  - rewrite 后继次幂, 乘后继, <- 归纳假设, 指数和运算律...
  - 排中 (β = 0) as [|Hβ0]. subst. rewrite 零次幂, 底数为一的幂, 乘于零, 零次幂...
    assert (积不为零: β * γ ≠ 0). intros H. apply 积为零 in H as []...
    排中 (α = 0) as [|Hα0]. subst. repeat rewrite 底数为零的幂...
    assert (幂不为零: α ^ β ≠ 0). intros H. apply 幂为零 in H...
    排中 (α = 1) as [|Hα1]. subst. repeat rewrite 底数为一的幂...
    外延 ξ Hξ.
    + rewrite 极限次幂 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]]. 2: apply 积为极限_右...
      rewrite 乘极限 in Hδ... apply 集族并除去 in Hδ as [ε [Hε Hδ]].
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. assert (Hεo: ε ⋵ 𝐎𝐍) by eauto.
      apply 序数传递 with (α ^ δ), 序数传递 with (α ^ (β * ε))...
      apply 幂运算保序... rewrite 归纳假设... apply 幂运算保序...
      rewrite <- (零次幂 α)... apply 幂运算保序...
    + rewrite 极限次幂 in Hξ... apply 集族并除去 in Hξ as [δ [Hδ Hξ]].
      apply 序数传递 with ((α ^ β) ^ δ)... rewrite <- 归纳假设...
      assert (Hδo: δ ⋵ 𝐎𝐍) by eauto. apply 幂运算保序, 乘法保序...
Qed.

(* 有限运算律 *)

Lemma 加法有限吸收律 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ω ⋸ α → n + α = α.
Proof with auto.
  intros α Hα n Hn Hle. 归纳 n.
  - rewrite 加于零...
  - rewrite <- 加一, 加法结合律, 无限加于一...
Qed.

Lemma 加法有限结合律 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, α + α * n = α * n + α.
Proof with auto.
  intros α Hα n Hn. 归纳 n.
  - rewrite 乘零, 加零, 加于零...
  - rewrite 乘后继... rewrite <- 归纳假设 at 2... rewrite 加法结合律...
Qed.

Lemma 乘法有限结合律 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, α * α ^ n = α ^ n * α.
Proof with auto.
  intros α Hα n Hn. 归纳 n.
  - rewrite 零次幂, 乘一, 乘于一...
  - rewrite 后继次幂... rewrite <- 归纳假设 at 2... rewrite 乘法结合律...
Qed.

Lemma 加法有限放大 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ∀β ∈ α * n, β ∈ α + β.
Proof with auto.
  intros α Hα n Hn. 归纳 n; intros β Hβ.
  - rewrite 乘零 in Hβ... simpl in Hβ. 空集归谬.
  - 排中 (β ∈ α * n)... assert (Hβo: β ⋵ 𝐎𝐍). eauto.
    rewrite 乘后继, <- 加法有限结合律 in Hβ...
    rewrite 序数可换 in H... apply 双重否定除去 in H as [].
    + apply 序数传递 with (α + α * n)... apply 加法保序...
    + rewrite H in Hβ...
Qed.

Lemma 乘法有限放大 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, ∀β ∈ α ^ n, β ≠ 0 → β ∈ α * β.
Proof with auto.
  intros α Hα n Hn β Hβ Hβ0.
  assert (H0: β ∉ α ^ 0). {
    intros H. rewrite 零次幂 in H...
    apply 后继除去 in H as []. 空集归谬. exfalso...
  }
  排中 (α = 0) as [|Hα0]. {
    subst. 排中 (n = 0). subst... exfalso...
    rewrite 底数为零的幂 in Hβ... simpl in Hβ. 空集归谬.
  }
  generalize dependent n. 归纳 n; intros.
  - exfalso...
  - 排中 (β ∈ α ^ n). apply 归纳假设...
    assert (Hβo: β ⋵ 𝐎𝐍). eauto.
    rewrite 后继次幂, <- 乘法有限结合律 in Hβ...
    rewrite 序数可换 in H... apply 双重否定除去 in H as [].
    + apply 序数传递 with (α * α ^ n)... apply 乘法保序...
    + rewrite H in Hβ...
Qed.

(** 消去律 **)

Lemma 加法消去律 : ∀ α β γ ⋵ 𝐎𝐍, α + β = α + γ → β = γ.
Proof with auto.
  intros α Hα β Hβ γ Hγ H.
  destruct (序数三歧 β Hβ γ Hγ) as [|[]]...
  - exfalso. apply 序数反自反 with (α + β)... rewrite H at 2. apply 加法保序...
  - exfalso. apply 序数反自反 with (α + β)... rewrite H at 1. apply 加法保序...
Qed.

Lemma 乘法消去律 : ∀ α β γ ⋵ 𝐎𝐍, α ≠ 0 → α * β = α * γ → β = γ.
Proof with auto.
  intros α Hα β Hβ γ Hγ H0 H.
  destruct (序数三歧 β Hβ γ Hγ) as [|[]]...
  - exfalso. apply 序数反自反 with (α * β)... rewrite H at 2. apply 乘法保序...
  - exfalso. apply 序数反自反 with (α * β)... rewrite H at 1. apply 乘法保序...
Qed.

Lemma 幂运算消去律 : ∀ α β γ ⋵ 𝐎𝐍, 1 ∈ α → α ^ β = α ^ γ → β = γ.
Proof with auto.
  intros α Hα β Hβ γ Hγ H1 H.
  destruct (序数三歧 β Hβ γ Hγ) as [|[]]...
  - exfalso. apply 序数反自反 with (α ^ β)... rewrite H at 2. apply 幂运算保序...
  - exfalso. apply 序数反自反 with (α ^ β)... rewrite H at 1. apply 幂运算保序...
Qed.

(** 弱保序 **)

Lemma 加法保序_弱右 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ⋸ β → γ + α ⋸ γ + β.
Proof.
  intros α β Hβ γ Hγ [].
  left. apply 加法保序; auto. right. congruence.
Qed.

Lemma 加法保序_弱左 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ⋸ β → α + γ ⋸ β + γ.
Proof with auto.
  intros α β Hβ γ Hγ Hle.
  assert (Hα: α ⋵ 𝐎𝐍). destruct Hle. eauto. congruence.
  超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 加零, 加零...
  - rewrite 加后继, 加后继, <- 后继弱保序...
  - apply 小于等于即包含... rewrite 加极限, 加极限... intros x Hx.
    apply 集族并除去 in Hx as [δ [Hδ Hx]]. assert (Hδo: δ ⋵ 𝐎𝐍). eauto.
    apply 集族并介入 with δ... apply 归纳假设 in Hδ as []...
    apply 序数传递 with (α + δ)... congruence.
Qed.

Lemma 乘法保序_弱右 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ⋸ β → γ * α ⋸ γ * β.
Proof with auto.
  intros α β Hβ γ Hγ [].
  排中 (γ = 0). subst. rewrite 乘于零, 乘于零... eauto.
  left. apply 乘法保序... right. congruence.
Qed.

Lemma 乘法保序_弱左 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ⋸ β → α * γ ⋸ β * γ.
Proof with auto.
  intros α β Hβ γ Hγ Hle.
  assert (Hα: α ⋵ 𝐎𝐍). destruct Hle. eauto. congruence.
  超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 乘零, 乘零...
  - rewrite 乘后继, 乘后继... apply 序数传递_弱 with (β * γ + α)...
    + apply 加法保序_弱左...
    + destruct Hle. left. apply 加法保序... right. congruence.
  - apply 小于等于即包含... rewrite 乘极限, 乘极限... intros x Hx.
    apply 集族并除去 in Hx as [δ [Hδ Hx]]. assert (Hδo: δ ⋵ 𝐎𝐍). eauto.
    apply 集族并介入 with δ... apply 归纳假设 in Hδ as []...
    apply 序数传递 with (α * δ)... congruence.
Qed.

Lemma 幂运算保序_弱右 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ⋸ β → γ ^ α ⋸ γ ^ β.
Proof with auto.
  intros α β Hβ γ Hγ Hγ1 [].
  排中 (γ = 1). subst. rewrite 底数为一的幂, 底数为一的幂... eauto.
  left. apply 幂运算保序... right. congruence.
Qed.

Lemma 幂运算保序_弱左 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ⋸ β → α ^ γ ⋸ β ^ γ.
Proof with auto.
  intros α β Hβ γ Hγ Hle.
  assert (Hα: α ⋵ 𝐎𝐍). destruct Hle. eauto. congruence.
  超限归纳 γ Hγ. 超限讨论 γ.
  - rewrite 零次幂, 零次幂...
  - rewrite 后继次幂, 后继次幂... apply 序数传递_弱 with (β ^ γ * α)...
    + apply 乘法保序_弱左...
    + destruct Hle. 2: right; congruence. left. apply 乘法保序...
      intros H1. apply 幂为零 in H1... subst. simpl in H0. 空集归谬.
  - 排中 (α = 0) as [|Hα0]. subst. rewrite 底数为零的幂...
    排中 (β = 0) as [|Hβ0]. {
      subst. destruct Hle. simpl in H. 空集归谬.
      subst. rewrite 底数为零的幂...
    }
    apply 小于等于即包含... rewrite 极限次幂, 极限次幂... intros x Hx.
    apply 集族并除去 in Hx as [δ [Hδ Hx]]. assert (Hδo: δ ⋵ 𝐎𝐍). eauto.
    apply 集族并介入 with δ... apply 归纳假设 in Hδ as []...
    apply 序数传递 with (α ^ δ)... congruence.
Qed.

(** 放大 **)

Lemma 加法放大 : ∀ α β ⋵ 𝐎𝐍, β ≠ 0 → α ∈ α + β.
Proof with auto.
  intros α Hα β Hβ H0. rewrite <- 加零 at 1... apply 加法保序...
Qed.

Lemma 加法弱放大 : ∀ α β ⋵ 𝐎𝐍, α ⋸ β + α.
Proof with auto.
  intros α Hα β Hβ. rewrite <- 加于零 at 1 3... apply 加法保序_弱左...
Qed.

Corollary 加法保序放大 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, α ∈ β → α ∈ β + γ.
Proof with auto.
  intros α β Hβ γ Hγ Hlt.
  排中 (γ = 0). subst. rewrite 加零...
  eapply 序数传递 with β... apply 加法放大...
Qed.

Lemma 乘法放大 : ∀ α β ⋵ 𝐎𝐍, α ≠ 0 → 1 ∈ β → α ∈ α * β.
Proof with auto.
  intros α Hα β Hβ Hα0 Hβ1. rewrite <- 乘一 at 1... apply 乘法保序...
Qed.

Lemma 乘法弱放大 : ∀ α β ⋵ 𝐎𝐍, β ≠ 0 → α ⋸ β * α.
Proof with auto.
  intros α Hα β Hβ Hβ0. rewrite <- 乘于一 at 1 3...
  apply 乘法保序_弱左, 小于即后继小于等于...
Qed.

Corollary 乘法保序放大 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ∈ β → α ∈ β * γ.
Proof with auto.
  intros α β Hβ γ Hγ Hγ0 Hlt.
  排中 (β = 0). subst. simpl in Hlt. 空集归谬.
  排中 (γ = 1). subst. rewrite 乘一...
  eapply 序数传递 with β... apply 乘法放大...
Qed.

Lemma 幂运算放大 : ∀ α β ⋵ 𝐎𝐍, 1 ∈ α → 1 ∈ β → α ∈ α ^ β.
Proof with auto.
  intros α Hα β Hβ Hα1 Hβ1. rewrite <- 一次幂 at 1... apply 幂运算保序...
Qed.

Lemma 幂运算弱放大 : ∀ α β ⋵ 𝐎𝐍, 1 ∈ β → α ⋸ β ^ α.
Proof with auto.
  intros α Hα β Hβ Hβ1. apply 序数嵌入非无穷降链... apply 幂运算为序数嵌入...
Qed.

Corollary 幂运算保序放大 : ∀ α, ∀ β γ ⋵ 𝐎𝐍, γ ≠ 0 → α ∈ β → α ∈ β ^ γ.
Proof with auto.
  intros α β Hβ γ Hγ Hγ0 Hlt.
  排中 (β = 0). subst. simpl in Hlt. 空集归谬.
  排中 (β = 1). {
    subst. apply 后继除去 in Hlt as []. 空集归谬.
    subst. rewrite 底数为一的幂... 
  }
  排中 (γ = 1). subst. rewrite 一次幂...
  eapply 序数传递 with β... apply 幂运算放大...
Qed.

Lemma 和为一 : ∀ α β ⋵ 𝐎𝐍, α + β = 1 → α = 0 ∧ β = 1 ∨ α = 1 ∧ β = 0.
Proof with auto.
  intros α Hα β Hβ H. 超限讨论 α.
  - rewrite 加于零 in H...
  - 超限讨论 β.
    + rewrite 加零 in H...
    + exfalso.  rewrite <- (加一 β), <- 加法结合律, 加一 in H...
      apply 后继是单射 in H... apply 和为零 in H as [H _]... apply 后继非空 with α...
    + exfalso. apply 非零极限序数不小于ω in 极限... apply 序数反自反 with 1... rewrite <- H at 2.
      eapply 序数传递_右弱... apply 序数传递_弱 with β... apply 加法弱放大...
  - exfalso.
    排中 (β = 0). {
      subst. rewrite 加零 in H...
      apply 序数为极限当且仅当它不为后继 in 极限... apply 极限. exists 0...
    }
    apply 非零极限序数不小于ω in 极限... apply 序数反自反 with 1... rewrite <- H at 2.
    eapply 序数传递... apply 序数传递_左弱 with α... apply 加法放大...
Qed.

Lemma 积为一 : ∀ α β ⋵ 𝐎𝐍, α * β = 1 → α = 1 ∧ β = 1.
Proof with auto.
  intros α Hα β Hβ H. 超限讨论 β.
  - rewrite 乘零 in H... exfalso...
  - rewrite 乘后继 in H... apply 和为一 in H as [[]|[]]...
    + apply 积为零 in H as []...
      * exfalso. subst...
      * split... subst...
    + rewrite H0 in H. rewrite 乘于零 in H... exfalso...
  - exfalso.
    排中 (α = 0). subst. rewrite 乘于零 in H...
    排中 (α = 1). {
      subst. rewrite 乘于一 in H...
      apply 序数为极限当且仅当它不为后继 in 极限... apply 极限. exists 0...
    }
    apply 非零极限序数不小于ω in 极限... apply 序数反自反 with 1... rewrite <- H at 2.
    eapply 序数传递_右弱... apply 序数传递_弱 with β... apply 乘法弱放大...
Qed.

Lemma 幂为一 : ∀ α β ⋵ 𝐎𝐍, α ^ β = 1 → α = 1 ∨ β = 0.
Proof with auto.
  intros α Hα β Hβ H. 超限讨论 β.
  - rewrite 零次幂 in H...
  - rewrite 后继次幂 in H... apply 积为一 in H as []...
  - 排中 (α = 1)... 排中 (α = 0). subst. rewrite 底数为零的幂 in H...
    exfalso. apply 非零极限序数不小于ω in 极限... apply 序数反自反 with 1... rewrite <- H at 2.
    eapply 序数传递_右弱... apply 序数传递_弱 with β... apply 幂运算弱放大...
Qed.

Theorem ω幂对加法的吸收律 : ∀β ⋵ 𝐎𝐍, ∀α ∈ β, ω ^ α + ω ^ β = ω ^ β.
Proof with auto.
  超限归纳 β Hβ. intros α Hαβ. assert (Hα: α ⋵ 𝐎𝐍). eauto.
  超限讨论 β. 空集归谬.
  - apply 后继除去 in Hαβ as [].
    + rewrite 后继次幂... rewrite <- 一加ω等于ω at 3...
      rewrite 乘法分配律, 乘一, <- 加法结合律, 归纳假设...
      rewrite <- (乘一 (ω ^ β)) at 1...
      rewrite <- 乘法分配律, 一加ω等于ω...
    + subst. rewrite 后继次幂...
      rewrite <- (乘一 (ω ^ β)) at 1...
      rewrite <- 乘法分配律, 一加ω等于ω...
  - 外延 x Hx.
    + rewrite 加极限 in Hx... 2: apply 幂为极限_右... 2: intros H; apply 幂为零 in H...
      apply 集族并除去 in Hx as [y [Hy Hx]]. rewrite 极限次幂 in Hy...
      apply 集族并除去 in Hy as [z [Hz Hy]]. assert (Hzo: z ⋵ 𝐎𝐍). eauto.
      apply 序数传递 with (ω ^ α + y)... 排中 (α ∈ z).
      * apply 序数传递 with (ω ^ α + ω ^ z)... apply 加法保序...
        rewrite 归纳假设... apply 幂运算保序...
      * assert (z ⋸ α). 反证. apply 序数可换 in 反设...
        assert (α⁺ ∈ β). apply 极限序数有其任意元素的后继...
        apply 序数传递 with (ω ^ α + ω ^ α⁺)... apply 加法保序...
        apply 序数传递 with (ω ^ z)... apply 幂运算保序... apply 小于等于即小于后继...
        rewrite 归纳假设... apply 幂运算保序...
    + rewrite 极限次幂 in Hx...
      apply 集族并除去 in Hx as [y [Hy Hx]]. assert (Hyo: y ⋵ 𝐎𝐍). eauto.
      rewrite 加极限... 2: apply 幂为极限_右... 2: intros H; apply 幂为零 in H...
      apply 集族并介入 with (ω ^ y). apply 幂运算保序...
      apply 序数传递_右弱 with (ω ^ y)... apply 加法弱放大...
Qed.
