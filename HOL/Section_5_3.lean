import Mathlib.Tactic
import HOL.Basic

/-!

# Higher-Order logics, Section 5.3: Inductive Definitions

Main results of this section:

- The definition of the transitive closure of a relation.
- The minimality theorem for the transitive closure.

-/


/-- The transitive closure of a binary relation. -/
def bi_trans_closure : ( e → e → t) → e → e → t :=
  fun R x y => ∀ X : e → e → t,
    (∀ z w, R z w → X x y) → (∀ z w u, X z w → X w u → X z u) → X x y


/-- The minimality theorem for the transitive closure. -/
theorem minimality_of_trans_closure : ∀ R S : e → e → t, ∀ x y : e,
(∀ z w, R z w → S x y) → (∀ z w u, S z w → S w u → S z u) → (bi_trans_closure R) x y → S x y
:= by
  intro R S x y
  intro h1 h2 h3
  rw [bi_trans_closure] at h3
  specialize h3 S
  specialize h3 h1 h2
  exact h3
  -- exact h3 S h1 h2
