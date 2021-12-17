(** Coq coding by choukh, Oct 2021 **)

Require Export BBST.Notation.Class.
Require Export BBST.Axiom.Meta.
Require Export BBST.Axiom.Extensionality.
Require Export BBST.Axiom.Separation.
Require Export BBST.Axiom.Pairing.
Require Export BBST.Axiom.Union.
Require Export BBST.Axiom.Replacement.
Require Export BBST.Definition.Include.
Require Export BBST.Definition.Singleton.
Require Export BBST.Definition.Complement.
Require Export BBST.Definition.BinaryUnion.
Require Export BBST.Definition.Intersect.
Require Export BBST.Definition.BinaryIntersect.
Require Export BBST.Definition.EpsilonOrdering.
Require Export BBST.Definition.Omega.
Require Export BBST.Definition.NatEmbedding.
Require Export BBST.Definition.Function.
Require Export BBST.Definition.Restriction.
Require Import BBST.Lemma.FunctionManeuver.
Require Import BBST.Theory.OrderingOnOmega.

Definition 为序数 := λ α, 为传递集 α ∧ ϵ良序 α.
Notation 𝐎𝐍 := 为序数.

Fact 序数为传递集 : ∀α ⋵ 𝐎𝐍, 为传递集 α.
Proof. intros. apply H. Qed.

Fact 序数是ϵ三歧 : ∀α ⋵ 𝐎𝐍, ϵ三歧 α.
Proof. intros. apply H. Qed.

Fact 序数是ϵ良基 : ∀α ⋵ 𝐎𝐍, ϵ良基 α.
Proof. intros. apply H. Qed.

Fact 序数是ϵ良序 : ∀α ⋵ 𝐎𝐍, ϵ良序 α.
Proof. intros. apply H. Qed.

Global Hint Immediate 序数为传递集 序数是ϵ三歧 序数是ϵ良基 序数是ϵ良序 : core.

Lemma 𝐎𝐍为传递类 : 为传递类 𝐎𝐍.
Proof with auto.
  intros β α Hβα [传 良]. split.
  - intros δ γ Hδγ Hγβ.
    assert (Hγα: γ ∈ α). apply 传 with β...
    assert (Hδα: δ ∈ α). apply 传 with γ...
    apply 良 with γ...
  - apply ϵ良序集的任意子集是ϵ良序 with α...
    apply 传递集即其元素都为其子集...
Qed.

Lemma 序数反自反 : ∀α ⋵ 𝐎𝐍, α ∉ α.
Proof. intros α Hα 反设. cut (α ∉ α); auto. apply Hα; auto. Qed.

Lemma 序数传递 : ∀ α β, ∀γ ⋵ 𝐎𝐍, α ∈ β → β ∈ γ → α ∈ γ.
Proof. intros. apply 序数为传递集 with β; auto. Qed.

Lemma 序数半可换 : ∀ α β ⋵ 𝐎𝐍, α ∈ β → ¬ β ⋸ α.
Proof with auto.
  intros α Hα β Hβ H [].
  - apply 序数反自反 with α... apply 序数为传递集 with β...
  - subst. apply 序数反自反 with α...
Qed.

Lemma 小于即真包含 : ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ α ⊂ β.
Proof with auto.
  intros α Hα β Hβ. split; intros.
  - split. apply 传递集即其元素都为其子集...
    intros Heq. apply 序数反自反 with α... subst...
  - set (β - α) as δ. assert (良基: ϵ良基 β)...
    destruct (良基 δ) as [ξ [Hξ 最小]].
    apply 真包含则补集非空... apply 分离为子集.
    apply 分离除去 in Hξ as [Hξ Hξ']...
    assert (Hξo: ξ ⋵ 𝐎𝐍). apply 𝐎𝐍为传递类 with β...
    replace α with ξ... 外延 Hx.
    + 反证. assert (Hxδ: x ∈ δ). apply 分离介入... apply 序数为传递集 with ξ...
      apply 最小 in Hxδ. apply 序数半可换 in Hx... apply 𝐎𝐍为传递类 with ξ...
    + 反证. apply H in Hx as Hxβ. assert (三歧: ϵ三歧 β)...
      destruct (三歧 x Hxβ ξ Hξ) as [|[]]... subst...
      apply Hξ'. apply 序数为传递集 with x...
Qed.

Lemma 小于等于即包含 : ∀ α β ⋵ 𝐎𝐍, α ⋸ β ↔ α ⊆ β.
Proof with auto.
  intros α Hα β Hβ. split.
  - intros []. apply 小于即真包含... subst...
  - intros. 排中 (α = β)... left. apply 小于即真包含...
Qed.

Ltac 序数外延 := apply 包含的反对称性; apply 小于等于即包含.

Lemma 序数的二元交为序数 : ∀ α β ⋵ 𝐎𝐍, α ∩ β ⋵ 𝐎𝐍.
Proof with auto.
  intros α Hα β Hβ. split.
  - intros δ γ Hδγ Hγ. apply 二元交除去 in Hγ as [Hγα Hγβ].
    apply 二元交介入; apply 序数为传递集 with γ...
  - apply ϵ良序集的任意子集是ϵ良序 with α...
Qed.

Lemma 序数三歧 : ∀ α β ⋵ 𝐎𝐍, α = β ∨ α ∈ β ∨ β ∈ α.
Proof with auto.
  intros α Hα β Hβ.
  assert (Ho: α ∩ β ⋵ 𝐎𝐍). apply 序数的二元交为序数...
  assert (H1: α ∩ β ⊆ α)... assert (H2: α ∩ β ⊆ β)...
  apply 小于等于即包含 in H1 as [H1|H1], H2 as [H2|H2]...
  - exfalso. apply 序数反自反 with (α ∩ β)...
  - right. right. congruence.
  - right. left. congruence.
  - left. congruence.
Qed.

Lemma 序数可换 : ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ ¬ β ⋸ α.
Proof with auto.
  intros α Hα β Hβ. split. apply 序数半可换...
  intros H. 反证. destruct (序数三歧 α Hα β Hβ) as [|[]]...
Qed.

Lemma 𝐎𝐍良基 : ∀ A, A ≠ ∅ → A ⪽ 𝐎𝐍 → 有ϵ最小元 A.
Proof with auto.
  intros A 非空 子集. apply 非空介入 in 非空 as [α Hα].
  排中 (ϵ最小 α A). exists α... apply 德摩根定律' in H as []. exfalso...
  apply 非全是即存非 in H as [β [Hβ Hβα]]. apply 序数可换 in Hβα...
  assert (良基: ϵ良基 α). apply 序数是ϵ良基...
  destruct (良基 (α ∩ A)) as [μ [Hμ 最小]]... apply 非空除去. exists β...
  apply 二元交除去 in Hμ as [H1 H2]. exists μ. split...
  intros x Hx. 反证. apply 序数可换 in 反设 as Hxμ... apply 反设.
  apply 最小. apply 二元交介入... apply 序数为传递集 with μ...
Qed.

Theorem 序数集是ϵ良序 : ∀ A, A ⪽ 𝐎𝐍 → ϵ良序 A.
Proof with auto.
  intros. repeat split; intros α Hα.
  - apply 序数反自反...
  - intros β _ γ Hγ. apply 序数传递...
  - intros β Hβ. apply 序数三歧...
  - intros 子集. apply 𝐎𝐍良基...
Qed.

Corollary 由序数组成的传递集为序数 : ∀ A, A ⪽ 𝐎𝐍 → 为传递集 A → A ⋵ 𝐎𝐍.
Proof. intros A 子集 传递. split; auto. apply 序数集是ϵ良序; auto. Qed.

(* 布拉利-福尔蒂悖论 *)
Theorem 𝐎𝐍为真类 : 为真类 𝐎𝐍.
Proof with auto.
  intros [A HA]. set {x ∊ A | x ⋵ 𝐎𝐍} as Ω.
  assert (HΩ: ∀ α, α ⋵ 𝐎𝐍 ↔ α ∈ Ω). {
    split; intros H. apply 分离介入... apply 分离之条件 in H...
  }
  assert (Ω ⋵ 𝐎𝐍). { split.
  - intros α β Hαβ Hβ. apply HΩ.
    apply 𝐎𝐍为传递类 with β... apply HΩ...
  - apply 序数集是ϵ良序. apply HΩ.
  }
  apply HΩ in H as 自反. apply 序数反自反 with Ω...
Qed.

Local Hint Resolve 𝐎𝐍为传递类 : core.

Fact 零为序数 : ∅ ⋵ 𝐎𝐍.
Proof.
  split3. 1-2: firstorder using 空集定理.
  intros A H0 H. apply 含于空集即为空集 in H. easy.
Qed.
Global Hint Resolve 零为序数 : core.

Fact ω为序数 : ω ⋵ 𝐎𝐍.
Proof. split. apply ω为传递集. apply ω是ϵ良序. Qed.
Global Hint Resolve ω为序数 : core.

Fact ω为序数集 : ω ⪽ 𝐎𝐍.
Proof. intros. apply 𝐎𝐍为传递类 with ω; auto. Qed.

Theorem 序数的后继为序数 : ∀α ⋵ 𝐎𝐍, α⁺ ⋵ 𝐎𝐍.
Proof with eauto.
  intros α Hα. apply 由序数组成的传递集为序数.
  - intros x Hx. apply 二元并除去 in Hx as [].
    eauto. apply 单集除去 in H. subst...
  - apply 传递集的后继为传递集...
Qed.
Global Hint Resolve 序数的后继为序数 : core.

(** 序数的序 **)

(* α⁺是大于α的最小数 *)
Theorem 小于即后继小于等于 : ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ α⁺ ⋸ β.
Proof with auto.
  intros α Hα β Hβ. split.
  - intros Hlt. apply 小于等于即包含... intros x Hx.
    apply 后继除去 in Hx as []. apply 序数传递 with α... subst...
  - intros Hle. apply 序数可换... intros Hle'. apply 小于等于即包含 in Hle, Hle'...
    pose proof (包含的传递性 α⁺ β α Hle Hle'). apply 序数反自反 with α...
Qed.

Lemma 小于等于即小于后继 : ∀ α β ⋵ 𝐎𝐍, α ⋸ β ↔ α ∈ β⁺.
Proof.
  intros α Hα β Hβ. split.
  - intros []. auto. subst. auto.
  - intros H. apply 后继除去 in H as [].
    now left. now right.
Qed.

Theorem 后继保序 : ∀ α β ⋵ 𝐎𝐍, α ∈ β ↔ α⁺ ∈ β⁺.
Proof.
  intros α Hα β Hβ.
  rewrite 小于即后继小于等于, 小于等于即小于后继; auto. reflexivity.
Qed.

Theorem 后继是单射 : ∀ α β ⋵ 𝐎𝐍, α⁺ = β⁺ → α = β.
Proof.
  intros α Hα β Hβ 相等.
  apply 序数为传递集 in Hα, Hβ.
  rewrite 传递集即其后继的并等于自身 in Hα, Hβ. congruence.
Qed.

Corollary 后继弱保序 : ∀ α β ⋵ 𝐎𝐍, α ⋸ β ↔ α⁺ ⋸ β⁺.
Proof with auto.
  intros α Hα β Hβ. split; intros H.
  - destruct H. left. rewrite <- 后继保序... right. congruence.
  - destruct H. left. rewrite 后继保序... right. apply 后继是单射...
Qed.

Lemma 包含即小于后继 : ∀ α β ⋵ 𝐎𝐍, α ⊆ β ↔ α ∈ β⁺.
Proof.
  intros α Hα β Hβ. rewrite <- (小于等于即包含 α Hα β Hβ).
  exact (小于等于即小于后继 α Hα β Hβ).
Qed.

Lemma 序数传递_弱 : ∀ α β, ∀γ ⋵ 𝐎𝐍, α ⋸ β → β ⋸ γ → α ⋸ γ.
Proof with auto.
  intros α β γ Hγ H1 H2.
  assert (Hβ: β ⋵ 𝐎𝐍). destruct H2. eauto. congruence.
  assert (Hα: α ⋵ 𝐎𝐍). destruct H1. eauto. congruence.
  apply 小于等于即包含 in H1, H2...
  pose proof (包含的传递性 α β γ H1 H2). apply 小于等于即包含...
Qed.

Lemma 序数传递_右弱 : ∀ α β, ∀ γ ⋵ 𝐎𝐍, α ∈ β → β ⋸ γ → α ∈ γ.
Proof with eauto.
  intros α β γ Hγ Hαβ [Hβγ|Hβγ]. eapply 序数传递... subst...
Qed.

Lemma 序数传递_左弱 : ∀ α β, ∀ γ ⋵ 𝐎𝐍,  α ⋸ β → β ∈ γ → α ∈ γ.
Proof with eauto.
  intros α β γ Hγ [Hαβ|Hαβ] Hβγ. eapply 序数传递... subst...
Qed.

Theorem 序数不稠密 : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, α ∈ β⁺ → False.
Proof.
  intros. apply 序数可换 with β α; auto. eauto.
  apply 小于等于即小于后继 in H1; auto. eauto.
Qed.

Fact 小于则不等 : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, β ≠ α.
Proof. intros α Hα β 小于 相等. subst. apply 序数反自反 with α; auto. Qed.

Fact 序数不等于其后继 : ∀α ⋵ 𝐎𝐍, α ≠ α⁺.
Proof. intros α Hα. apply 小于则不等; auto. Qed.

Fact 大于零的序数不为零 : ∀α ⋵ 𝐎𝐍, ∅ ∈ α → α ≠ ∅.
Proof. intros α Hα H H0. subst. 空集归谬. Qed.
Global Hint Immediate 大于零的序数不为零 :core.

Fact 不为零的序数大于零 : ∀α ⋵ 𝐎𝐍, α ≠ ∅ → ∅ ∈ α.
Proof. intros α Hα H. destruct (序数三歧 α Hα ∅) as [|[]]; auto. easy. 空集归谬. Qed.
Global Hint Immediate 不为零的序数大于零 :core.

Fact 序数的后继大于零 : ∀α ⋵ 𝐎𝐍, ∅ ∈ α⁺.
Proof. intros α Hα. apply 不为零的序数大于零; auto. Qed.
Global Hint Immediate 序数的后继大于零 :core.

Fact 序数大于等于零 : ∀α ⋵ 𝐎𝐍, ∅ ⋸ α.
Proof. intros α Hα. apply 小于等于即包含; auto. Qed.
Global Hint Resolve 序数大于等于零 : core.

(** 下确界 **)

Theorem 序数集的交为序数 : ∀ A, A ⪽ 𝐎𝐍 → ⋂ A ⋵ 𝐎𝐍.
Proof with auto.
  intros A H. apply 由序数组成的传递集为序数.
  - intros x Hx. apply 交集除去 in Hx as [[α Hα] Hx]. apply 𝐎𝐍为传递类 with α...
  - intros x y Hx Hy. apply 交集除去 in Hy as [[α Hα] Hy].
    apply 交集介入. exists α... intros β Hβ. apply 序数传递 with y...
Qed.

Definition 为下界 := λ μ A, μ ⋵ 𝐎𝐍 ∧ ∀ξ ∈ A, μ ⋸ ξ.
Definition 为下确界 := λ μ A, 为下界 μ A ∧ ∀ ξ, 为下界 ξ A → ξ ⋸ μ.

(* 序数集的下确界 *)
Notation "'inf' A" := (⋂ A) (at level 9, only parsing).

Lemma 序数集的交为下界 : ∀ A, A ⪽ 𝐎𝐍 → 为下界 (inf A) A.
Proof with auto.
  intros. apply 序数集的交为序数 in H as 下界.
  split... intros α Hα. apply 小于等于即包含... apply 交得子集...
Qed.

Lemma 序数集的交为下确界 : ∀ A, A ≠ ∅ → A ⪽ 𝐎𝐍 → 为下确界 (inf A) A.
Proof with auto.
  intros. apply 非空介入 in H. split. apply 序数集的交为下界...
  intros μ [Hμ 最小]. apply 小于等于即包含... apply 序数集的交为序数...
  intros x Hx. apply 交集介入... intros y Hy.
  apply 最小 in Hy as Hle. apply 小于等于即包含 in Hle...
Qed.

Lemma 序数集内有其下确界 : ∀ A, A ≠ ∅ → A ⪽ 𝐎𝐍 → inf A ∈ A.
Proof with auto.
  intros A 非空 序数集.
  pose proof (序数集的交为下确界 A 非空 序数集) as [[Hinf 下界] 下确界].
  pose proof (序数集是ϵ良序 A 序数集) as [_ 良基].
  pose proof (良基 A 非空) as [μ [Hµ Hle]]...
  pose proof (下确界 μ) as []. split... 2: subst...
  exfalso. apply 序数可换 with μ (inf A)...
Qed.

Theorem 序数集的下确界 : ∀ A, A ≠ ∅ → A ⪽ 𝐎𝐍 → inf A ∈ A ∧ 为下确界 (inf A) A.
Proof with auto.
  intros. split. apply 序数集内有其下确界... apply 序数集的交为下确界...
Qed.

Fact 序数的下确界为空集 : ∀α ⋵ 𝐎𝐍, inf α = ∅.
Proof with auto.
  intros. 外延. 2: 空集归谬.
  apply 交集除去 in H0 as [[β Hβ] Hx].
  排中 (α = ∅). subst. 空集归谬. apply 不为零的序数大于零 in H0...
Qed.

Section 满足条件的最小序数.
Variable α : 集合.
Variable Hα : α ⋵ 𝐎𝐍.
Variable P : 性质.
Variable HP : P α.

Local Notation A := {β ∊ α⁺ | P β}.
Local Notation μ := (inf A).

Local Lemma A非空 : A ≠ ∅.
Proof. apply 非空除去. exists α. apply 分离介入; auto. Qed.

Local Lemma A为序数集 : A ⪽ 𝐎𝐍.
Proof. intros x Hx. apply 分离之父集 in Hx. eauto. Qed.

Lemma 满足条件的最小序数为之 : μ ⋵ 𝐎𝐍 ∧ P μ ∧ ∀β ⋵ 𝐎𝐍, P β → μ ⋸ β.
Proof with auto.
  pose proof (序数集的下确界 A A非空 A为序数集) as [Hμ [[Hμo Hle] _]].
  split3... apply 分离之条件 in Hμ... intros β Hβ H. 排中 (α⁺ ⋸ β).
  - left. apply 序数传递_右弱 with α⁺... apply 分离之父集 in Hμ...
  - apply Hle. apply 分离介入... apply 序数可换...
Qed.

Theorem 存在满足条件的最小序数 : ∃ μ, μ ⋵ 𝐎𝐍 ∧ P μ ∧ ∀β ⋵ 𝐎𝐍, P β → μ ⋸ β.
Proof. exists μ. apply 满足条件的最小序数为之. Qed.

End 满足条件的最小序数.

(** 上确界 **)

Theorem 序数集的并为序数 : ∀ A, A ⪽ 𝐎𝐍 → ⋃ A ⋵ 𝐎𝐍.
Proof with auto.
  intros A H. apply 由序数组成的传递集为序数.
  - intros α Hα. apply 并集除去 in Hα as [β [Hβ Hα]]. apply H in Hβ. eauto.
  - apply 传递集即其元素都为其子集.
    intros α Hα. apply 并集除去 in Hα as [β [Hβ Hα]]. eapply 包含的传递性 with β.
    apply 小于等于即包含... eauto. apply 并得父集...
Qed.

Corollary 序数的并为序数 : ∀α ⋵ 𝐎𝐍, ⋃ α ⋵ 𝐎𝐍.
Proof. intros. apply 序数集的并为序数. intros x Hx. eauto. Qed.

Corollary 序数的二元并为序数 : ∀ α β ⋵ 𝐎𝐍, α ∪ β ⋵ 𝐎𝐍.
Proof.
  intros α Hα β Hβ. apply 序数集的并为序数.
  intros x Hx. apply 配对除去 in Hx as []; subst; auto.
Qed.

Definition 为上界 := λ μ A, μ ⋵ 𝐎𝐍 ∧ ∀ξ ∈ A, ξ ⋸ μ.
Definition 为上确界 := λ μ A, 为上界 μ A ∧ ∀ ξ, 为上界 ξ A → μ ⋸ ξ.

(* 序数/序数集的上确界 *)
Notation "'sup' A" := (⋃ A) (at level 8, only parsing).

Lemma 序数集的并为上界 : ∀ A, A ⪽ 𝐎𝐍 → 为上界 (sup A) A.
Proof with auto.
  intros. apply 序数集的并为序数 in H as 上界.
  split... intros α Hα. apply 小于等于即包含... apply 并得父集...
Qed.

Lemma 序数集的并为上确界 : ∀ A, A ⪽ 𝐎𝐍 → 为上确界 (sup A) A.
Proof with auto.
  intros. split. apply 序数集的并为上界...
  intros μ [Hμ 最小]. apply 小于等于即包含...
  apply 序数集的并为序数... apply 所有元素都是子集则并集也是子集.
  intros β Hβ. apply 小于等于即包含...
Qed.

Lemma 序数的上确界小于等于自身 : ∀α ⋵ 𝐎𝐍, sup α ⋸ α.
Proof with auto.
  intros. apply 小于等于即包含... apply 序数的并为序数...
  apply 所有元素都是子集则并集也是子集.
  intros x Hx. apply 小于等于即包含... eauto.
Qed.

Lemma 后继序数的上确界为前驱 : ∀α ⋵ 𝐎𝐍, sup α⁺ = α.
Proof. intros. apply 传递集即其后继的并等于自身. auto. Qed.

Fact 零的上确界为自身 : sup ∅ = ∅.
Proof. exact 空集之并. Qed.

Fact ω的上确界为自身 : sup ω = ω.
Proof.
  apply 包含的反对称性.
  - apply 传递集即其并为其子集. auto.
  - intros n Hn. apply 并集介入 with n⁺; auto.
Qed.

(** 后继序数, 极限序数 **)

Definition 为后继序数 := λ α, ∃β ⋵ 𝐎𝐍, α = β⁺.
Notation 𝐒𝐔𝐂 := 为后继序数.

Definition 为极限序数 := λ α, α ⋵ 𝐎𝐍 ∧ sup α = α.
Notation 𝐋𝐈𝐌 := 为极限序数.

Fact 零为极限 : ∅ ⋵ 𝐋𝐈𝐌.
Proof. split. auto. exact 零的上确界为自身. Qed.

Fact ω为极限 : ω ⋵ 𝐋𝐈𝐌.
Proof. split. auto. exact ω的上确界为自身. Qed.
Global Hint Resolve ω为极限 : core.

Theorem 极限序数有其任意元素的后继 : ∀α ⋵ 𝐋𝐈𝐌, ∀β ∈ α, β⁺ ∈ α.
Proof with auto.
  intros α [Hα 极限] β 小于. assert (Hβ: β ⋵ 𝐎𝐍). eauto.
  apply 序数可换... intros [].
  - apply 包含即小于后继 in H... apply H in 小于. apply 序数反自反 with β...
  - subst. rewrite 后继序数的上确界为前驱 in 极限... apply 序数不等于其后继 with β...
Qed.

Fact 非零极限序数是归纳集 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → 归纳的 α.
Proof with auto.
  intros α [Hα 极限]. split.
  - destruct (序数三歧 α Hα ∅)...
  - apply 极限序数有其任意元素的后继. split...
Qed.

Theorem 序数要么为后继要么为极限 : ∀α ⋵ 𝐎𝐍, α ⋵ 𝐒𝐔𝐂 ∨ α ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros α H. 排中 (α ⋵ 𝐋𝐈𝐌)... left.
  apply 德摩根定律' in H0  as []... easy.
  assert (真包含: sup α ⊂ α). {
    split... apply 小于等于即包含... apply 序数的并为序数...
    apply 序数的上确界小于等于自身...
  }
  apply 真包含则存在独有元素 in 真包含 as [β [Hβ Hβ']].
  assert (Hoβ: β ⋵ 𝐎𝐍). eauto.
  exists β. split... 反证. destruct (序数三歧 α H β⁺) as [|[]]...
  - apply 序数不稠密 with α β...
  - apply Hβ'. apply 并集介入 with β⁺...
Qed.

Ltac 后继序数展开 := match goal with | H: ?α ⋵ 𝐒𝐔𝐂 |- _ =>
  let β := fresh "β" in let Hβ := fresh "Hβ" in let H' := fresh "H" in
  destruct H as [β [Hβ H]]; subst α;
  rename β into α; rename Hβ into H'
end.

Theorem 序数为极限当且仅当它不为后继 : ∀α ⋵ 𝐎𝐍, α ⋵ 𝐋𝐈𝐌 ↔ ¬ α ⋵ 𝐒𝐔𝐂.
Proof with auto.
  intros. split.
  - intros [_ 极限] Hα. 后继序数展开.
    rewrite 后继序数的上确界为前驱 in 极限... apply 序数不等于其后继 with α...
  - intros 非后继. destruct (序数要么为后继要么为极限 α H) as []... easy.
Qed.

Ltac 超限讨论 α := match goal with | H : α ⋵ 𝐎𝐍 |- _ =>
  let H0 := fresh "H0" in
  排中 (α = ∅) as [H0|H0]; [subst α|
    destruct (序数要么为后继要么为极限 α H) as [?后继|?极限]; [clear H0; 后继序数展开|]
  ]
end.

Lemma 为后继的上确界在序数集内 : ∀ A, A ⪽ 𝐎𝐍 → sup A ⋵ 𝐒𝐔𝐂 → sup A ∈ A.
Proof with auto.
  intros A HA [α [Hα Heq]]. apply 序数集的并为上确界 in HA as H.
  destruct H as [[Hs 上界] 上确界]. 排中 (为上界 α A).
  - exfalso. apply 上确界 in H. rewrite Heq in H. apply 序数可换 with α α⁺...
  - apply 德摩根定律' in H as []. exfalso...
    apply 非全是即存非 in H as [β [Hβ H]]. apply 序数可换 in H...
    pose proof (上界 β Hβ) as []; rewrite Heq in H0.
    exfalso. apply 序数不稠密 with β α... congruence.
Qed.

Lemma 在序数集外的上确界为极限 : ∀ A, A ⪽ 𝐎𝐍 → sup A ∉ A → sup A ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros A HA H. assert (Hs: sup A ⋵ 𝐎𝐍). apply 序数集的并为序数...
  apply 序数为极限当且仅当它不为后继... intros Hsuc. apply H.
  apply 为后继的上确界在序数集内...
Qed.

Lemma 极限序数集的并为极限 : ∀ A, A ⪽ 𝐋𝐈𝐌 → ⋃ A ⋵ 𝐋𝐈𝐌.
Proof with auto.
  intros. 排中 (sup A ∈ A). apply H...
  apply 在序数集外的上确界为极限... apply H.
Qed.

Lemma 非零极限序数不小于ω : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → ω ⋸ α.
Proof with auto.
  intros n [Hn H] Hne. 反证. apply 序数可换 in 反设...
  讨论 n... assert (n ⋵ 𝐎𝐍). apply ω为序数集...
  rewrite 后继序数的上确界为前驱 in H...
  apply 序数反自反 with n... rewrite H at 2...
Qed.

(** 超限归纳 **)

Theorem 超限归纳法 : ∀ P : 性质, (∀α ⋵ 𝐎𝐍, ((∀β ∈ α, P β) → P α)) → ∀α ⋵ 𝐎𝐍, P α.
Proof with auto.
  intros P 归纳 α Hα.
  assert (总有更小: ∀ ξ ⋵ 𝐎𝐍, ¬ P ξ → ∃β ∈ ξ, ¬ P β). {
    intros ξ Hξ 否定. apply 非全是即存非...
  }
  反证. set {ξ ∊ α | ¬ P ξ} as α'.
  destruct (𝐎𝐍良基 α') as [μ [Hμ μ最小]]. {
    (* 非空 *) destruct (总有更小 α) as [β [Hβ 否定]]...
    apply 非空除去. exists β... apply 分离介入...
  } {
    (* 序数集 *) intros ξ Hξ. apply 分离之父集 in Hξ. eauto.
  }
  apply 分离除去 in Hμ as [Hμ μ否定].
  destruct (总有更小 μ) as [ν [Hν 否定]]... eauto.
  assert (Hν': ν ∈ α'). apply 分离介入... apply 序数传递 with μ...
  apply μ最小 in Hν'. apply 序数可换 with ν μ... eauto. eauto.
Qed.

Ltac 超限归纳 α Hα :=
  match goal with
    | |- ∀α ⋵ 𝐎𝐍, _ => intros α Hα; pattern α
    | Hα: α ⋵ 𝐎𝐍 |- _ => pattern α
  end;
  match goal with |- ?P α => let IH := fresh "归纳假设" in
    generalize dependent α; apply (超限归纳法 P); intros α Hα IH
  end.

Tactic Notation "超限归纳" simple_intropattern(α) simple_intropattern(Hα) := 超限归纳 α Hα.
Tactic Notation "超限归纳" simple_intropattern(α) := 超限归纳 α ?Hα.
Tactic Notation "超限归纳" := let α := fresh "α" in let Hα := fresh "Hα" in 超限归纳 α Hα.

Section 超限递归.
Variable G : 函数类型.

Local Definition 为前段 := λ α f, 为函数 f ∧ dom f = α⁺ ∧ ∀ β, β ⋸ α → f[β] = G (f ↾ β).

Lemma 前段性质 : ∀α ⋵ 𝐎𝐍, ∀β ∈ α, ∀ f g, 为前段 α f → 为前段 β g → f ↾ β⁺ = g.
Proof with auto.
  intros α Hα β Hβα f g [函f [定f 值f]] [函g [定g 值g]].
  assert (Hβo: β ⋵ 𝐎𝐍). eauto.
  assert (Hβf: β⁺ ⊆ dom f). rewrite 定f. apply 小于等于即包含... left. rewrite <- 后继保序...
  apply 函数之外延... apply 限制为函数... rewrite 限制之定义域...
  intros γ Hγβ. rewrite 限制之定义域 in Hγβ... rewrite 限制之应用...
  assert (Hγ: γ ⋵ 𝐎𝐍). eauto.
  generalize dependent Hγβ. generalize dependent γ.
  超限归纳 γ Hγ. intros Hγβ.
  assert (Hγα: γ ∈ α⁺). apply 序数传递 with β⁺... rewrite <- 后继保序...
  rewrite 值f, 值g... 2-3: apply 小于等于即小于后继... f_equal.
  assert (Hγf: γ ⊆ dom f). rewrite 定f. apply 小于等于即包含...
  assert (Hγg: γ ⊆ dom g). rewrite 定g. apply 小于等于即包含...
  apply 函数之外延. 1-2: apply 限制为函数... rewrite 限制之定义域, 限制之定义域...
  intros δ Hδ. rewrite 限制之定义域 in Hδ... rewrite 限制之应用, 限制之应用...
  apply 归纳假设... apply 序数传递 with γ...
Qed.

Local Lemma 前段唯一 : ∀α ⋵ 𝐎𝐍, uniqueness (为前段 α).
Proof with auto.
  intros α Hα f g [函f [定f 值f]] [函g [定g 值g]].
  apply 函数之外延... congruence. intros β Hβlt.
  rewrite 定f in Hβlt. assert (Hβ: β ⋵ 𝐎𝐍). eauto.
  apply 小于等于即小于后继 in Hβlt as Hβle... rewrite 值f, 值g... f_equal.
  assert (Hβf: β ⊆ dom f). rewrite 定f. apply 小于即真包含...
  assert (Hβg: β ⊆ dom g). rewrite 定g. apply 小于即真包含...
  apply 函数之外延. 1-2: apply 限制为函数...
  - rewrite 限制之定义域, 限制之定义域...
  - intros γ Hγβ. rewrite 限制之定义域 in Hγβ...
    assert (Hγ: γ ⋵ 𝐎𝐍). eauto.
    rewrite 限制之应用, 限制之应用...
    generalize dependent Hγβ. generalize dependent γ.
    超限归纳 γ Hγ. intros Hγβ.
    assert (Hγlt: γ ∈ α⁺). apply 序数传递 with β...
    apply 小于等于即小于后继 in Hγlt as Hγle...
    rewrite 值f, 值g... f_equal.
    assert (Hγf: γ ⊆ dom f). rewrite 定f. apply 小于即真包含...
    assert (Hγg: γ ⊆ dom g). rewrite 定g. apply 小于即真包含...
    apply 函数之外延. 1-2: apply 限制为函数...
    + rewrite 限制之定义域, 限制之定义域...
    + intros δ Hδ. rewrite 限制之定义域 in Hδ...
      rewrite 限制之应用, 限制之应用...
      apply 归纳假设... apply 序数传递 with γ...
Qed.

(* Section中的前段指前α前段 *)
Section 前段构造.
Variable α : 集合.
Variable Hα : α ⋵ 𝐎𝐍.
Variable 前段存在 : ∀β ∈ α, ∃ f, 为前段 β f.

Local Lemma 前段存在唯一 : ∀β ∈ α, ∃!f, 为前段 β f.
Proof.
  intros. rewrite <- unique_existence. split.
  apply 前段存在. auto. apply 前段唯一. eauto.
Qed.

Local Definition 前段 := λ ξ, 描述 (为前段 ξ).

Local Lemma 前段规范 : ∀β ∈ α, 为前段 β (前段 β).
Proof. intros. unfold 前段. apply 描述公理. apply 前段存在唯一. auto. Qed.

Local Lemma 前段定义域: ∀β ∈ α, dom (前段 β) = β⁺.
Proof. intros. apply 前段规范 in H as [_ [定 _]]. auto. Qed.

Local Lemma 前段值相等: ∀ β γ ∈ α, ∀ x y z, <x, y> ∈ 前段 β → <x, z> ∈ 前段 γ → y = z.
Proof with auto.
  intros β Hβα γ Hγα x y z Hxy Hxz.
  assert (Hβ: β ⋵ 𝐎𝐍). eauto.
  assert (Hγ: γ ⋵ 𝐎𝐍). eauto.
  apply 前段规范 in Hβα as Hf, Hγα as Hg.
  copy Hf as [函f [定f _]]. 函数|-Hxy.
  copy Hg as [函g [定g _]]. 函数|-Hxz.
  assert (Hxβ: x ∈ β⁺). rewrite <- 定f. 域.
  assert (Hxγ: x ∈ γ⁺). rewrite <- 定g. 域.
  destruct (序数三歧 β Hβ γ Hγ) as [|[]]. congruence.
  - rewrite <- (限制之应用 (前段 γ) β⁺)... f_equal. symmetry.
    apply 前段性质 with γ... rewrite 定g.
    apply 小于等于即包含... left. rewrite <- 后继保序...
  - rewrite <- (限制之应用 (前段 β) γ⁺)... f_equal.
    apply 前段性质 with β... rewrite 定f.
    apply 小于等于即包含... left. rewrite <- 后继保序...
Qed.

(* 前段集 *)
Local Definition F := {前段 β | β ∊ α}.
(* α前段 *)
Local Definition h := ⋃ F ∪ {<α, G (⋃ F)>,}.

Local Lemma 前段并为函数: 为函数 (⋃ F).
Proof with auto. split.
  - (* 为序偶集 *) intros p Hp.
    apply 集族并除去 in Hp as [β [Hβ Hp]].
    apply 前段规范 in Hβ as [[序偶 _] _]...
  - (* 单值 *) intros x y z Hxy Hxz.
    apply 集族并除去 in Hxy as [β [Hβα Hxy]].
    apply 集族并除去 in Hxz as [γ [Hγα Hxz]].
    apply 前段值相等 with β γ x...
Qed.

Local Lemma 前段并之定义域 : dom ⋃ F = α.
Proof with auto.
  unfold F. rewrite 函数集族并之定义域. 外延.
  - apply 集族并除去 in H as [β [Hβ Hx]]. rewrite 前段定义域 in Hx...
    apply 后继除去 in Hx as []... apply 序数传递 with β... subst...
  - apply 集族并介入 with x... rewrite 前段定义域...
Qed.

Local Lemma α不在前段并之定义域 : α ∉ dom ⋃ F.
Proof. intros H. rewrite 前段并之定义域 in H. apply 序数反自反 with α; auto. Qed.

Local Lemma α前段为函数 : 为函数 h.
Proof. apply 函数加点. apply 前段并为函数. apply α不在前段并之定义域. Qed.

Local Lemma α前段之定义域 : dom h = α⁺.
Proof.
  unfold h. rewrite 函数加点之定义域.
  replace (dom ⋃ F) with α; auto. rewrite 前段并之定义域; auto. 
Qed.

Local Lemma α前段之值 : ∀ β, β ⋸ α → h[β] = G (h ↾ β).
Proof with auto.
  intros β [].
  - assert (Hβ: β ⋵ 𝐎𝐍); eauto. assert (Hβα := H).
    rewrite <- 前段并之定义域 in H. 定|-H as [y Hp].
    apply 集族并除去 in Hp as H'. destruct H' as [γ [Hγα Hpγ]].
    apply 前段规范 in Hγα as H'. destruct H' as [函 [定 值]].
    assert (Hγ: γ ⋵ 𝐎𝐍); eauto.
    assert (Hβγ: β ∈ γ⁺). rewrite <- 定. 域.
    assert (Hhβ: h[β] = G (前段 γ ↾ β)). {
      rewrite <- 值. 2: apply 小于等于即小于后继...
      apply 函数应用. apply α前段为函数. apply 左并介入... 函数|-Hpγ...
    }
    rewrite Hhβ. f_equal. 外延 x Hx; 序偶分离|-Hx; 序偶分离-|...
    + apply 左并介入. apply 集族并介入 with γ...
    + apply 二元并除去 in Hp0 as []...
      * apply 集族并除去 in H as [δ [Hδ H]].
        assert (Ha: a ∈ dom (前段 γ)). rewrite 定. apply 序数传递 with β...
        函数-|. apply 前段值相等 with δ γ a... 函数-|.
      * apply 单集除去 in H. apply 序偶相等 in H as [H _]; subst a.
        exfalso. apply 序数半可换 with α β...
  - rewrite H. apply 函数应用. apply α前段为函数. apply 右并介入...
    replace (⋃ F) with (h ↾ α)... rewrite <- 前段并之定义域.
    apply 函数加点之左限制. apply 前段并为函数. apply α不在前段并之定义域.
Qed.

Local Theorem α前段为之 : 为前段 α h.
Proof. split3. apply α前段为函数. apply α前段之定义域. apply α前段之值. Qed.

End 前段构造.

Local Lemma 前段存在 : ∀α ⋵ 𝐎𝐍, ∃ f, 为前段 α f.
Proof. 超限归纳. exists (h α). apply α前段为之; auto. Qed.

Local Definition 超限递归关系 := λ x y, ∃ f, 为前段 x f ∧ y = f[x].

Local Lemma 超限递归关系有函数性 : ∀x ⋵ 𝐎𝐍, ∃!y, 超限递归关系 x y.
Proof with auto.
  intros. destruct (前段存在 x) as [f Hf]...
  exists (f[x]). split. exists f...
  intros y [g [Hg Hy]]. subst. f_equal. apply 前段唯一 with x...
Qed.

Definition 超限递归 := λ x, 描述 (超限递归关系 x).

Lemma 超限递归满足其关系 : ∀α ⋵ 𝐎𝐍, 超限递归关系 α (超限递归 α).
Proof.
  intros. unfold 超限递归. apply 描述公理.
  apply 超限递归关系有函数性. auto.
Qed.

Global Opaque 超限递归.

Theorem 超限递归定理 : ∀α ⋵ 𝐎𝐍, 超限递归 α = G (超限递归 ↑ α).
Proof with auto.
  intros α Hα.
  pose proof (超限递归满足其关系 α Hα) as [f [[函f [定f 值f]] 超f]].
  rewrite 超f, 值f... f_equal.
  rewrite 替代式限制, 类函数替代式限制... 2: rewrite 定f...
  apply 替代之外延. intros β Hβα. apply 序偶相等. split...
  assert (Hβ: β ⋵ 𝐎𝐍). eauto.
  pose proof (超限递归满足其关系 β Hβ) as [g [[函g [定g 值g]] 超g]].
  rewrite 值f, 超g, 值g... f_equal.
  rewrite <- (限制到父再子 f β β⁺)... f_equal.
  apply 前段性质 with α... split... split...
Qed.

End 超限递归.

Module 超限递归模板_三指定.
Section 超限递归模板_三指定.
Variable y₀ : 集合.
Variable F₁ : 函数类型.
Variable F₂ : 函数类型.

Local Definition G关系 := λ f y,
  (dom f = ∅ → y₀ = y) ∧ (dom f ≠ ∅ →
    (dom f ⋵ 𝐒𝐔𝐂 → F₁ f[sup (dom f)] = y) ∧
    (dom f ⋵ 𝐋𝐈𝐌 → F₂ f = y)
  ).

Local Lemma G关系有函数性 : ∀ f, dom f ⋵ 𝐎𝐍 → ∃! y, G关系 f y.
Proof with auto; try easy.
  intros. 排中 (dom f = ∅).
  - exists y₀. split... intros y Hy. apply Hy...
  - destruct (序数要么为后继要么为极限 (dom f) H) as [后继|极限].
    + exists (F₁ f[sup (dom f)]). split.
      * split... intros _. split... intros 极限.
        apply 序数为极限当且仅当它不为后继 in 极限...
      * intros y Hy. apply Hy...
    + exists (F₂ f). split.
      * split... intros _. split... intros 后继.
        apply 序数为极限当且仅当它不为后继 in 后继...
      * intros y Hy. apply Hy...
Qed.

Local Definition G := λ f, 描述 (G关系 f).

Local Lemma G规范 : ∀ f, dom f ⋵ 𝐎𝐍 → G关系 f (G f).
Proof. intros. unfold G. apply 描述公理. apply G关系有函数性. auto. Qed.

Definition 三指定 := 超限递归 G.
Local Notation f := 三指定.

Theorem 三指定_0 : f ∅ = y₀.
Proof with auto.
  intros. unfold 三指定. rewrite 超限递归定理...
  symmetry. eapply G规范; rewrite 类函数限制之定义域...
Qed.

Theorem 三指定_后继 : ∀α ⋵ 𝐎𝐍, f α⁺ = F₁ (f α).
Proof with auto.
  intros. unfold 三指定. rewrite 超限递归定理...
  rewrite (类函数限制之应用 (超限递归 G) α⁺)...
  replace α with (sup (dom (超限递归 G ↑ α⁺))) at 3.
  symmetry. apply G规范. 1-4: rewrite 类函数限制之定义域...
  exists α... apply 后继序数的上确界为前驱...
Qed.

Theorem 三指定_极限 : ∀α ⋵ 𝐋𝐈𝐌, α ≠ ∅ → f α = F₂ (f ↑ α).
Proof with auto.
  intros α 极限 非零. copy 极限 as [Hα Hsup].
  unfold 三指定. rewrite 超限递归定理...
  symmetry. apply G规范; rewrite 类函数限制之定义域...
Qed.

End 超限递归模板_三指定.
End 超限递归模板_三指定.
