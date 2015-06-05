(* This file another solution Ex 8.9 used by Coq.Arith.Even in Coq'Art. *)

Open Scope nat_scope.
(* In Coq'Art's solution, following even definition is used. *)
(* But, in this solution, this definition is not used. *)
(* Inductive even : nat -> Prop := *)
(* | O_even : even 0 *)
(* | SS_even : forall n:nat, even n -> even (S (S n)). *)

(* Hint Resolve O_even SS_even. *)

Require Import Coq.Arith.Even.

Hint Resolve even_O even_S.
Hint Resolve odd_S even_S.

Fixpoint mult2 (n:nat) : nat :=
  match n with
    | O => 0
    | S p => S (S (mult2 p))
  end.

Theorem even_mult2 :
  forall n:nat, even (mult2 n).
Proof.
  induction n.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Theorem sum_even :
  forall n p:nat, even n -> even p -> even (n+p).
Proof.
  intros n p H0 H1.
  apply even_even_plus.
  trivial.
  auto.
Qed.