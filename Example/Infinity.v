(** Coq coding by choukh, Oct 2021 **)

Require Import BBST.Axiom.Meta.
Require Import BBST.Definition.Include.
Require Import BBST.Definition.Emptyset.
Require Import BBST.Definition.Singleton.
Require Import BBST.Definition.Successor.

Axiom ℕ : 集合.

Axiom 零是自然数 : ∅ ∈ ℕ.
Axiom 一是自然数 : ∅⁺ ∈ ℕ.
Axiom 二是自然数 : ∅⁺⁺ ∈ ℕ.
Axiom 三是自然数 : ∅⁺⁺⁺ ∈ ℕ.

Axiom 以此类推 : ∀n ∈ ℕ, n⁺ ∈ ℕ.

Axiom 这不是自然数 : {{∅,},} ∉ ℕ.
Axiom 这也不是自然数 : {{{∅,},},} ∉ ℕ.
(* ヽ(`Д´)ﾉ *)
