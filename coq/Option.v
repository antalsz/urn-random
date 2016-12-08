From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Haskell.
Open Scope haskell_scope.

Arguments Some {A} _.
  
Theorem omap_id {A} :
  omap id =1 @id (option A).
Proof. by case. Qed.

Theorem omap_id' {A} (oa : option A) :
  omap id oa = oa.
Proof. by case oa. Qed.

Theorem omap_comp {A B C} (f1 : B -> C) (f2 : A -> B) :
  omap f1 ∘ omap f2 =1 omap (f1 ∘ f2).
Proof. by case. Qed.

Theorem omap_comp' {A B C} (f1 : B -> C) (f2 : A -> B) (oa : option A) :
  omap f1 (omap f2 oa) = omap (f1 ∘ f2) oa.
Proof. by case oa. Qed.

Theorem oapp_omap {A B C} (f1 : B -> C) (f2 : A -> B) (r : C) :
  oapp f1 r ∘ omap f2 =1 oapp (f1 ∘ f2) r.
Proof. by case. Qed.

Theorem oapp_omap' {A B C} (f1 : B -> C) (f2 : A -> B) (r : C) (oa : option A) :
  oapp f1 r (omap f2 oa) = oapp (f1 ∘ f2) r oa.
Proof. by case oa. Qed.
