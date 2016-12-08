From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Coq.ZArith.ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Lemma pos_eqbP : Equality.axiom Pos.eqb.
Proof.
  move=> p q; case Heq: (p =? q)%positive; constructor.
  - by apply Pos.eqb_eq.
  - by apply Pos.eqb_neq.
Qed.
 
Definition positive_eqMixin := EqMixin pos_eqbP.
Canonical positive_eqType := EqType positive positive_eqMixin.

Lemma N_eqbP : Equality.axiom N.eqb.
Proof.
  move=> p q; case Heq: (p =? q)%N; constructor.
  - by apply N.eqb_eq.
  - by apply N.eqb_neq.
Qed.
 
Definition N_eqMixin := EqMixin N_eqbP.
Canonical N_eqType := EqType N N_eqMixin.

Lemma Npos_succ_swap (p : positive) :
  N.pos (Pos.succ p) = N.succ (N.pos p).
Proof. done. Qed.
