(** Coq coding by choukh, Sep 2021 **)

Require Import Coq.Unicode.Utf8_core.

Theorem 三段论 : ∀ P Q : Prop, P → (P → Q) → Q.
Proof.
  intros P Q H1 H2. apply H2. apply H1.
Qed.

Print 三段论.
(*
  三段论 = λ (P Q : Prop) (H1 : P) (H2 : P → Q),
    H2 H1 : ∀ P Q : Prop, P → (P → Q) → Q
*)

Theorem 三段论' : ∀ P Q : Prop, P → (P → Q) → Q.
Proof.
  intros P Q H1 H2. exact (H2 H1).
Qed.

(* 练习1-1 *)
Theorem 蕴含的传递性 : ∀ P Q R : Prop, (P → Q) → (Q → R) → P → R.
Proof.
  admit.
Admitted.

Locate "∧".
(* Notation "x ∧ y" := (and x y) : type_scope (default interpretation) *)

Locate "∨".
(* Notation "x ∨ y" := (or x y) : type_scope (default interpretation) *)

Locate "¬".
(* Notation "¬ x" := (not x) : type_scope (default interpretation) *)

Print not.
(* not = λ A : Prop, A → False : Prop → Prop *)

Print False.
(* Inductive False : Prop := *)

Fact 矛盾 : False.
Proof.
  (* 无法构造 *)
Abort.

Check or.
(* or : Prop → Prop → Prop *)

Print or.
(*
  Inductive or (A B : Prop) : Prop :=
	  | or_introl : A → or A B
    | or_intror : B → or A B
*)

Fact 实质蕴含 : ∀ P Q, (¬ P ∨ Q) → (P → Q).
Proof.
  intros P Q Hor HP.
  destruct Hor as [HnP|HnQ].
  - firstorder.
  - apply HnQ.
Qed.

Check and.
(* and : Prop → Prop → Prop *)

Print and.
(*
  Inductive and (A B : Prop) : Prop :=
    | conj : A → B → and A B
*)

Theorem 德摩根定律' : ∀ P Q, ¬ (P ∨ Q) → (¬ P ∧ ¬ Q).
Proof.
  intros P Q H. split.
  - intros HP. apply H. exact(or_introl HP).
  - intros HP. apply H. exact(or_intror HP).
Qed.

Theorem 同一律 {A: Type} : ∀ x : A, x = x.
Proof.
  intros x. reflexivity.
Qed.

Theorem 非存是则全非 {A: Type} : ∀ P : A → Prop,
  (¬ ∃ x, P x) → ∀ x, ¬ P x.
Proof.
  intros P H. intros x HPx. apply H.
  exists x. apply HPx.
Qed.

Require Import BBST.Axiom.Meta.

Theorem 双重否定除去 : ∀ P, ¬ ¬ P → P.
Proof.
  intros P H. 排中 P.
  - (* P成立 *) apply H0.
  - (* P不成立 *) exfalso. apply H. apply H0.
Qed.

(* 练习1-2 *)
Theorem 德摩根定律2 : ∀ P Q, ¬ (P ∧ Q) → (¬ P ∨ ¬ Q).
Proof.
  intros P Q H. 排中 P.
  - admit. (* 不要使用firstorder *)
  - admit.
Admitted.

(* 练习1-3 *)
Theorem 皮尔士定律 : ∀ P Q : Prop, ((P → Q) → P) → P.
Proof.
  intros P Q H. 排中 (P → Q).
  - admit.
  - 反证. admit.
Admitted.

Fact 属于或不属于 : ∀ x y, x ∈ y ∨ x ∉ y.
Proof.
  intros x y. 排中 (x ∈ y).
  - left. apply H.
  - right. apply H.
Qed.

Fact 属于或不属于' : ∀ x y, x ∈ y ∨ x ∉ y.
Proof.
  intros x y. exact (排中律 (x ∈ y)).
Qed.

Theorem 集合非存是则全非 : ∀ A (P : 性质),
  ¬ (∃x ∈ A, P x) → (∀x ∈ A, ¬ P x).
Proof.
  intros A P H x Hx HPx.
  apply H. exists x. split.
  - apply Hx.
  - apply HPx.
Qed.

(* 练习1-4 *)
Theorem 集合非全是则存非 : ∀ A (P : 性质),
  ¬ (∀x ∈ A, P x) → (∃x ∈ A, ¬ P x).
Proof.
  intros A P H. 反证.
  admit. (* 不要使用firstorder *)
Admitted.

Check inhabited.
(* inhabited : Type → Prop *)

Print inhabited.
(* Inductive inhabited (A : Type) : Prop :=
  inhabits : A → inhabited A *)

Fact 存在集合 : ∃ x : 集合, x = x.
Proof.
  destruct 论域非空 as [a].
  exists a. reflexivity.
Qed.

Module 常元.

Axiom X : 集合.

Fact 存在集合' : ∃ x : 集合, x = x.
Proof.
  exists X. reflexivity.
Qed.

Fact 属于X或不属于X : ∀ x, x ∈ X ∨ x ∉ X.
Abort.

End 常元.
