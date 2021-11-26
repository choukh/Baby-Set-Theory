(** Coq coding by choukh, Nov 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.
Require Import BBST.Arith.Nat.
Require Import BBST.Arith.Ord.

Local Hint Immediate ω为序数集 : core.
Local Hint Resolve 加法为序数嵌入 乘法为序数嵌入 : core.
Local Hint Resolve 一为序数 𝐎𝐍为传递类 : core.
Local Hint Resolve 大于一的序数不等于零 :core.

Section 左加法不动点.
Variable ξ : 集合.
Variable Hξ : ξ ⋵ 𝐎𝐍.
Variable ξ不为零 : ξ ≠ 0.

Definition σ := 不动点枚举 (λ α, ξ + α).

Lemma σ为序数运算 : 为序数运算 σ.
Proof. apply 不动点枚举为序数运算. auto. Qed.
Local Hint Resolve σ为序数运算 : core.

Lemma σ为左加法不动点 : ∀α ⋵ 𝐎𝐍, ξ + (σ α) = σ α.
Proof. apply 不动点枚举枚举之. auto. Qed.

Lemma σ_0 : σ ∅ = ξ * ω.
Proof with auto.
  apply 包含的反对称性.
  - apply 小于等于即包含... unfold σ. rewrite 不动点枚举_0...
    apply 最小不动点为之... rewrite <- (乘一 ξ) at 1... rewrite <- 乘法分配律, 加法有限吸收律...
  - intros x Hx. rewrite 乘极限 in Hx...
    apply 集族并除去 in Hx as [n [Hn Hx]].
    apply 序数传递 with (ξ * n)... clear Hx. 归纳 n.
    + rewrite 乘零... apply 不等于零的序数大于零...
      unfold σ. rewrite <- 不动点枚举枚举之... intros H. apply 和为零 in H as []...
    + rewrite 乘后继, <- 加法有限结合律, <- σ为左加法不动点... apply 加法保序...
Qed.

Lemma σ_后继 : ∀α ⋵ 𝐎𝐍, σ α⁺ = (σ α)⁺.
Proof with auto.
  intros. apply 包含的反对称性.
  - apply 小于等于即包含... unfold σ. rewrite 不动点枚举_后继... fold σ.
    apply 后继不动点为之... rewrite 加后继, σ为左加法不动点...
  - intros x Hx. apply 小于等于即小于后继 in Hx... 2: eauto.
    apply 序数传递_左弱 with (σ α)... apply 不动点枚举在后继处递增...
Qed.

Lemma σ_极限 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → σ α = ⋃ {σ β | β ∊ α}.
Proof. apply 不动点枚举_极限. Qed.

Theorem σ表达式 : ∀α ⋵ 𝐎𝐍, σ α = ξ * ω + α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 加零... apply σ_0.
  - rewrite σ_后继, 加后继, 归纳假设...
  - rewrite σ_极限, 加极限... f_equal. apply 替代之外延...
Qed.

End 左加法不动点.

Section 左乘法不动点.
Variable ξ : 集合.
Variable Hξ : ξ ⋵ 𝐎𝐍.
Variable ξ大于一 : 1 ∈ ξ.

Lemma 左乘法非平凡 : ∀α ⋵ 𝐎𝐍, ξ * α⁺ ≠ α⁺.
Proof with auto.
  intros. rewrite 乘后继... intros Heq. apply 序数反自反 with α⁺...
  rewrite <- Heq at 2. apply 序数传递_右弱 with (α + ξ)...
  - rewrite <- 加一... apply 加法保序...
  - apply 加法弱保序_左... apply 序数嵌入非无穷降链...
Qed.
Local Hint Immediate 左乘法非平凡 : core.

Definition π := 不动点枚举 (λ α, ξ * α).

Lemma π为序数运算 : 为序数运算 π.
Proof. apply 不动点枚举为序数运算. auto. Qed.
Local Hint Resolve π为序数运算 : core.

Lemma π为左乘法不动点 : ∀α ⋵ 𝐎𝐍, ξ * (π α) = π α.
Proof. apply 不动点枚举枚举之. auto. Qed.

Lemma π_0 : π ∅ = 0.
Proof with auto.
  apply 包含的反对称性.
  - apply 小于等于即包含... unfold π. rewrite 不动点枚举_0...
    apply 最小不动点为之... rewrite 乘零...
  - intros x Hx. simpl in Hx. 空集归谬.
Qed.

Lemma π_1不为零 :  π 1 ≠ 0.
Proof with auto.
  intros H. rewrite <- π_0 in H. apply 序数嵌入为类单射 in H...
  apply 后继非空 with ∅... apply 不动点枚举为序数嵌入...
Qed.

Lemma π_1不为一 :  π 1 ≠ 1.
Proof with auto.
  intros H. assert (H1: ξ * 1 =  1). rewrite <- H. apply π为左乘法不动点...
  rewrite 乘一 in H1... apply 序数反自反 with 1... congruence.
Qed.
Local Hint Immediate π_1不为零 π_1不为一 : core.

Lemma π_1 : π 1 = ξ ^ ω.
Proof with auto.
  apply 包含的反对称性.
  - apply 小于等于即包含... unfold π. simpl. rewrite 不动点枚举_后继... fold π.
    apply 后继不动点为之...
    + rewrite <- (一次幂 ξ) at 1... rewrite <- 指数和运算律, 加法有限吸收律...
    + rewrite π_0. apply 不等于零的序数大于零...
      intros H. apply 幂为零 in H... subst. simpl in ξ大于一. 空集归谬.
  - intros x Hx. rewrite 极限次幂 in Hx...
    apply 集族并除去 in Hx as [n [Hn Hx]].
    apply 序数传递 with (ξ ^ n)... clear Hx. 归纳 n.
    + rewrite 零次幂... apply 不等于零和一的序数大于一...
    + rewrite 后继次幂, <- 乘法有限结合律, <- π为左乘法不动点... apply 乘法保序...
Qed.

Lemma π_后继 : ∀α ⋵ 𝐎𝐍, π α⁺ = π α + π 1.
Proof with auto.
  intros. apply 包含的反对称性.
  - apply 小于等于即包含... unfold π. rewrite 不动点枚举_后继... fold π.
    apply 后继不动点为之... rewrite 乘法分配律, π为左乘法不动点, π为左乘法不动点... apply 加法放大_右...
  - intros x Hx. rewrite 加极限 in Hx... 2: apply 不动点为极限...
    apply 集族并除去 in Hx as [y [Hy Hx]].
    rewrite π_1, 极限次幂 in Hy... apply 集族并除去 in Hy as [n [Hn Hy]].
    apply 序数传递 with (π α + y)... apply 序数传递 with (π α + ξ ^ n)...
    apply 加法保序... clear Hy. 归纳 n.
    + rewrite 零次幂, 加一... apply 极限序数有其任意元素的后继.
      apply 不动点为极限... apply 不动点枚举在后继处递增...
    + rewrite 后继次幂, <- π为左乘法不动点, <- (π为左乘法不动点 α⁺)...
      rewrite <- 乘法有限结合律, <- 乘法分配律... apply 乘法保序...
Qed.

Lemma π_极限 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → π α = ⋃ {π β | β ∊ α}.
Proof. apply 不动点枚举_极限. Qed.

Theorem π表达式 : ∀α ⋵ 𝐎𝐍, π α = ξ ^ ω * α.
Proof with auto.
  超限归纳. 超限讨论 α.
  - rewrite 乘零... apply π_0.
  - rewrite π_后继, 乘后继, π_1, 归纳假设...
  - rewrite π_极限, 乘极限... f_equal. apply 替代之外延...
Qed.

End 左乘法不动点.
