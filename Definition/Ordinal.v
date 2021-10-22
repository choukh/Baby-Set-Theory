(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.EpsilonOrdering.
Require Import BBST.Definition.Omega.
Require Import BBST.Notation.Class.

Definition 为序数 := λ α, 为传递集 α ∧ ϵ良序 α.
Notation 𝐎𝐍 := 为序数.

Theorem 序数是序数集 : ∀α ⋵ 𝐎𝐍, α ⪽ 𝐎𝐍.
Proof with auto.
  intros α [传 良] β Hβ. split.
  - intros δ γ Hδγ Hγβ.
    assert (Hγα: γ ∈ α). apply 传 with β...
    assert (Hδα: δ ∈ α). apply 传 with γ...
    apply 良 with γ...
  - apply ϵ良序集的任意子集是ϵ良序 with α...
    apply 传递集即其元素都为其子集...
Qed.
