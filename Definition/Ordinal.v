(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Axiom.Extensionality.
Require Import BBST.Axiom.Separation.
Require Import BBST.Definition.Complement.
Require Import BBST.Definition.BinaryIntersect.
Require Export BBST.Definition.EpsilonOrdering.
Require Export BBST.Definition.Omega.
Require Export BBST.Notation.Class.

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

Lemma 序数的交为序数 : ∀ α β ⋵ 𝐎𝐍, α ∩ β ⋵ 𝐎𝐍.
Proof with auto.
  intros α Hα β Hβ. split.
  - intros δ γ Hδγ Hγ. apply 二元交除去 in Hγ as [Hγα Hγβ].
    apply 二元交介入; apply 序数为传递集 with γ...
  - apply ϵ良序集的任意子集是ϵ良序 with α...
Qed.

Lemma 序数三歧 : ∀ α β ⋵ 𝐎𝐍, α = β ∨ α ∈ β ∨ β ∈ α.
Proof with auto.
  intros α Hα β Hβ.
  assert (Ho: α ∩ β ⋵ 𝐎𝐍). apply 序数的交为序数...
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

Corollary 由序数组成的传递集是序数 : ∀ A, A ⪽ 𝐎𝐍 → 为传递集 A → A ⋵ 𝐎𝐍.
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
