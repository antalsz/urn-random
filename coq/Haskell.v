From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Coq.Program.Basics.

Delimit Scope haskell_scope with hs.
Open Scope haskell_scope.

Notation "f '$' x" := (f x) (left associativity, at level 98, only parsing) : haskell_scope.
Notation "g '∘' f" := (g \o f) (left associativity, at level 50) : haskell_scope.
Notation "'_∘_'"   := (fun g f => g ∘ f) : haskell_scope.
Notation flip      := Basics.flip.
Notation uncurry   := prod_curry.
