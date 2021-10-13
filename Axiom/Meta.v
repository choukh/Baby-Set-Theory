(** Coq coding by choukh, Sep 2021 **)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Setoids.Setoid.

Axiom 排中律 : ∀ P, P ∨ ¬ P.

Tactic Notation "排中" constr(P) :=
  destruct (排中律 P).
Tactic Notation "排中" constr(P) "as" simple_intropattern(L) :=
  destruct (排中律 P) as L.

Ltac 反证 := match goal with
  |- ?G => destruct (排中律 G) as [?正设|?反设]; [assumption|exfalso]
end.

Theorem 双重否定除去 : ∀ P, ¬ ¬ P → P.
Proof.
  intros P H. 反证.
  apply H. apply 反设.
Qed.

Theorem 德摩根定律 : ∀ P Q, ¬ (P ∨ Q) → (¬ P ∧ ¬ Q).
Proof.
  intros P Q H. split.
  - intros HP. apply H. left. apply HP.
  - intros HP. apply H. right. apply HP.
Qed.

Axiom 集合 : Type.
Axiom 属于 : 集合 → 集合 → Prop.

Declare Scope 集合域.
Open Scope 集合域.

Notation "x ∈ y" := (  属于 x y) (at level 70) : 集合域.
Notation "x ∉ y" := (¬ 属于 x y) (at level 70) : 集合域.

Notation "∀ x .. y ∈ A , P" :=
  (∀ x, x ∈ A → (.. (∀ y, y ∈ A → P) ..))
  (at level 200, x binder, right associativity) : 集合域.

Notation "∃ x .. y ∈ A , P" :=
  (∃ x, x ∈ A ∧ (.. (∃ y, y ∈ A ∧ P) ..))
  (at level 200, x binder, right associativity) : 集合域.

Notation "'∃' ! x .. y , P" :=
  (ex (unique (λ x, .. (ex (unique (λ y, P))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃' ! '/ '  x .. y ,  '/ ' P ']'") : 集合域.

Notation "'∃' ! x .. y ∈ A , P" :=
  (∃! x, x ∈ A ∧ (.. (∃! y, y ∈ A ∧ P) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∃' ! '/ '  x .. y  ∈  A ,  '/ ' P ']'") : 集合域.

Notation 性质 := (集合 → Prop).

Lemma 非全非即存是 : ∀ A (P : 性质),
   ¬ (∀ x ∈ A, ¬ P x) ↔ (∃ x ∈ A, P x).
Proof. firstorder. 反证. firstorder. Qed.

Lemma 非全是即存非 : ∀ A (P : 性质),
  ¬ (∀ x ∈ A, P x) ↔ (∃ x ∈ A, ¬ P x).
Proof.
  firstorder. 反证. apply H.
  intros x Hx. 反证. firstorder.
Qed.

Lemma 非存是即全非 : ∀ A (P : 性质),
  ¬ (∃ x ∈ A, P x) ↔ (∀ x ∈ A, ¬ P x).
Proof. firstorder. Qed.

Lemma 非存非即全是 : ∀ A (P : 性质),
  ¬ (∃ x ∈ A, ¬ P x) ↔ (∀ x ∈ A, P x).
Proof. firstorder. 反证. firstorder. Qed.

Axiom 论域非空 : inhabited 集合.

Axiom 描述 : 性质 → 集合.
Axiom 描述公理 : ∀ P, (∃! x, P x) → P (描述 P).
