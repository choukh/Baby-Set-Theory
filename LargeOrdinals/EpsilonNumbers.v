(** Coq coding by choukh, Dec 2021 **)

Require Import BBST.Theory.Ordinal.
Require Import BBST.Theory.OrdinalOperation.
Require Import BBST.Arith.Nat.
Require Import BBST.Arith.Ord.
Require Import BBST.Arith.Tetration.

Local Hint Immediate ω为序数集 : core.
Local Hint Resolve 𝐎𝐍为传递类 幂运算为序数嵌入 : core.
Local Hint Resolve 左迭代为序数运算 顶迭代为序数运算 : core.

Definition ε := 不动点枚举 (幂运算 ω).

Lemma ε为序数运算 : 为序数运算 ε.
Proof. apply 不动点枚举为序数运算. auto. Qed.

Lemma ε为序数嵌入 : 为序数嵌入 ε.
Proof. apply 不动点枚举为序数嵌入. auto. Qed.
Local Hint Resolve ε为序数运算 ε为序数嵌入 : core.

Lemma ε数为不动点 : ∀α ⋵ 𝐎𝐍, ω ^ (ε α) = ε α.
Proof. apply 不动点枚举枚举之. auto. Qed.

Lemma ε数不为零 : ∀α ⋵ 𝐎𝐍, ε α ≠ ∅.
Proof with auto.
  intros α Hα. apply 不动点不为零... rewrite 零次幂... auto using 零不为一.
Qed.

Lemma ε数不为一 : ∀α ⋵ 𝐎𝐍, ε α ≠ 1.
Proof with auto.
  intros α Hα. assert (ω ^ ε α = ε α). apply ε数为不动点...
  intros H0. rewrite H0, 一次幂 in H...
  apply 序数反自反 with 1. apply ω为序数集... rewrite <- H at 2...
Qed.

Lemma ε数大于一 : ∀α ⋵ 𝐎𝐍, 1 ∈ ε α.
Proof with auto.
  intros. apply 不为零和一的序数大于一... apply ε数不为零... apply ε数不为一...
Qed.
Local Hint Resolve ε数不为零 ε数不为一 ε数大于一 : core.

Theorem ε_0 : ε ∅ = ω ^^ᴸ ω.
Proof with auto.
  apply 包含的反对称性.
  - apply 小于等于即包含... unfold ε. rewrite 不动点枚举_0...
    apply 最小不动点为之... rewrite <- 左迭代后继次, 左迭代在ω后继处不递增...
  - intros x Hx. rewrite 左迭代极限次 in Hx...
    apply 集族并除去 in Hx as [n [Hn Hx]].
    apply 序数传递 with (ω ^^ᴸ n)... clear Hx. 归纳 n.
    + rewrite 左迭代零次, <- ε数为不动点... apply 幂运算放大...
    + rewrite 左迭代后继次, <- ε数为不动点... apply 幂运算保序...
Qed.

Theorem ε_后继_ω塔 : ∀α ⋵ 𝐎𝐍, ε α⁺ = (ω ^^ᵀ ω) (ε α)⁺.
Proof. intros. unfold ε. rewrite 不动点枚举_后继, 顶迭代极限次; auto. Qed.

Theorem ε_极限 : 极限处连续 ε.
Proof. apply 不动点枚举_极限. Qed.

(* ε'顶ω塔 := 以ε数的后继为顶的ω塔 *)

Fact ε'顶ω塔0层 : ∀α ⋵ 𝐎𝐍, (ω ^^ᵀ 0) (ε α)⁺ = (ε α)⁺.
Proof. intros. rewrite 顶迭代零次; auto. Qed.

Fact ε'顶ω塔1层 : ∀α ⋵ 𝐎𝐍, (ω ^^ᵀ 1) (ε α)⁺ = ε α * ω.
Proof. intros. simpl. rewrite 顶迭代后继次, ε'顶ω塔0层, 后继次幂, ε数为不动点; auto. Qed.

Fact ε'顶ω塔2层 : ∀α ⋵ 𝐎𝐍, (ω ^^ᵀ 2) (ε α)⁺ = ε α ^ ω.
Proof. intros. simpl. rewrite 顶迭代后继次, ε'顶ω塔1层, 指数积运算律, ε数为不动点; auto. Qed.

Fact ε'顶ω塔3层 : ∀α ⋵ 𝐎𝐍, (ω ^^ᵀ 3) (ε α)⁺ = ε α ^ (ε α ^ ω).
Proof with auto.
  intros. simpl. rewrite 顶迭代后继次, ε'顶ω塔2层...
  rewrite <- 一加ω等于ω at 2...
  rewrite 指数和运算律, 一次幂, 指数积运算律, ε数为不动点...
Qed.

Lemma ε'顶ω塔n'层等于ω顶ε塔n层 : ∀α ⋵ 𝐎𝐍, ∀n ∈ ω, n ≠ 0 → (ω ^^ᵀ n⁺) (ε α)⁺ = (ε α ^^ᵀ n) ω.
Proof with auto.
  intros α Hα n Hn. 归纳 n; intros H1. exfalso...
  排中 (n = 0). subst. rewrite ε'顶ω塔2层, 顶迭代一次...
  rewrite 顶迭代后继次, 顶迭代后继次, 顶迭代后继次, <- 归纳假设, 顶迭代后继次...
  rewrite <- ε数为不动点 at 2... rewrite <- 指数积运算律... f_equal.
  rewrite <- ε数为不动点 at 2... rewrite <- 指数和运算律... f_equal.
  讨论 n. exfalso...
  rewrite <- ε数为不动点 at 2... rewrite 顶迭代后继次... symmetry.
  apply ω幂对加法的吸收律... clear H H1 归纳假设 Hn.
  归纳 n. rewrite 顶迭代零次...
  rewrite 顶迭代后继次... apply 序数传递_右弱 with ((ω ^^ᵀ n) (ε α)⁺)... apply 幂运算弱放大...
Qed.

Lemma ε'顶ω塔极限等于ω顶ε塔极限 : ∀α ⋵ 𝐎𝐍, (ω ^^ᵀ ω) (ε α)⁺ = (ε α ^^ᵀ ω) ω.
Proof with auto.
  intros. rewrite 顶迭代极限次, 顶迭代极限次...
  rewrite (弱保序无穷序列极限与起始无关 2)... 2: apply 顶迭代有限弱保序...
  rewrite (弱保序无穷序列极限与起始无关 1)... 2: apply 顶迭代有限弱保序...
  simpl. rewrite 弱递增无穷序列极限与起始无关... 2: apply 顶迭代有限弱递增...
  f_equal. apply 替代之外延. intros n Hn. apply 分离除去 in Hn as [Hn Hn'].
  apply ε'顶ω塔n'层等于ω顶ε塔n层... intros H0. apply Hn'. subst...
Qed.

Theorem ε_后继_ε塔 : ∀α ⋵ 𝐎𝐍, ε α⁺ = (ε α ^^ᴸ ω).
Proof with auto.
  intros. rewrite ε_后继_ω塔, ε'顶ω塔极限等于ω顶ε塔极限, 无限顶迭代等于左迭代...
  rewrite <- ε数为不动点... apply 幂运算放大...
Qed.

Local Notation "f ′" := (不动点枚举 f) (format "f ′", at level 9).
Local Notation 𝗔 := 任意不动点.
Local Notation 𝗥 := 序数递归.

Theorem 最小不动点表达为任意不动点 : ∀ φ, 为序数嵌入 φ →
  φ′ ∅ ≠ ∅ → φ′′ ∅ = 𝗔 φ′ (φ′ ∅).
Proof with auto.
  intros φ φ嵌入 H0.
  assert (H1: 为序数嵌入 φ′). subst. apply 不动点枚举为序数嵌入...
  assert (H2: φ′ ∅ ⋵ 𝐎𝐍). rewrite 不动点枚举_0. apply 最小不动点为之...
  assert (H3: φ′′ ∅ ⋵ 𝐎𝐍). subst. rewrite 不动点枚举_0. apply 最小不动点为之...
  assert (H4: 𝗔 φ′ (φ′ ∅) ⋵ 𝐎𝐍). apply 不动点为之...
  apply 包含的反对称性.
  - apply 小于等于即包含... rewrite 不动点枚举_0.
    apply 最小不动点为之... apply 不动点为之...
  - intros x Hx. apply 集族并除去 in Hx as [n [Hn Hx]].
    apply 序数传递 with (𝗥 (φ′ ∅) φ′ n)... clear Hx. 归纳 n.
    + rewrite 序数递归_0, <- (不动点枚举枚举之 φ′)... apply 序数嵌入保序...
      apply 不为零的序数大于零... apply 不动点不为零...
    + rewrite 序数递归_后继, <- (不动点枚举枚举之 φ′)... apply 序数嵌入保序...
Qed.

Definition ζ := ε′.

Fact ζ为序数嵌入 : 为序数嵌入 ζ.
Proof. apply 不动点枚举为序数嵌入. auto. Qed.
Local Hint Resolve ζ为序数嵌入 : core.

Fact ζ_0不为零 : ζ 0 ≠ 0.
Proof. apply 不动点不为零; auto. Qed.
Local Hint Resolve ζ_0不为零 : core.

Fact ζ_0 : ζ 0 = 𝗔 ε (ε 0).
Proof. apply 最小不动点表达为任意不动点; auto. Qed.

Fact ζ_后继 : ∀α ⋵ 𝐎𝐍, ζ α⁺ = 𝗔 ε (ζ α)⁺.
Proof. intros. unfold ζ. rewrite 不动点枚举_后继; auto. Qed.

Fact ζ_极限 : 极限处连续 ζ.
Proof. apply 不动点枚举_极限. Qed.

Definition η := ζ′.

Fact η为序数嵌入 : 为序数嵌入 η.
Proof. apply 不动点枚举为序数嵌入. auto. Qed.

Fact η_0不为零 : η 0 ≠ 0.
Proof. apply 不动点不为零; auto. Qed.

Fact η_0 : η 0 = 𝗔 ζ (ζ 0).
Proof. apply 最小不动点表达为任意不动点; auto. Qed.

Fact η_后继 : ∀α ⋵ 𝐎𝐍, η α⁺ = 𝗔 ζ (η α)⁺.
Proof. intros. unfold η. rewrite 不动点枚举_后继; auto. Qed.

Fact η_极限 : 极限处连续 η.
Proof. apply 不动点枚举_极限. Qed.
