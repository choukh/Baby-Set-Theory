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
