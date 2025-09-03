import Lean

/-!

# Higher-Order logics

This file defines the basic types and axioms for higher-order logics (HOL).

-/


/-- A type representing propositions.
For easy implementation of built-in tactics, we define a type `t` that is equal to `Prop`. -/
def t: Type := Prop

/-- A type representing entities.
`opaque` guarantees that no built-in axioms or definitions sneaks into the implementation. -/
opaque e : Type



namespace Classicism

/-!
The Rule of Equivalence: If `⊢ ∀ x, R x ↔ S x` then `⊢ R = S` (as predicates).

We add it as an axiom but enforce (by a custom tactic) that the antecedent
must be supplied by a previously established global lemma/theorem, not a local
hypothesis introduced inside the current proof.  This approximates the desired
"inference rule" behaviour without reifying the object language.

You should invoke the axiom only via the tactic `applyEquiv h`, where `h` is
the NAME (identifier) of a global lemma of type `∀ x, R x ↔ S x`.  If you try
to use a local hypothesis, the tactic rejects it (we approximate this by
requiring `h` to be a global constant).
-/

private axiom ruleOfEquiv_ax {R S : e → Prop} (h : ∀ x : e, R x ↔ S x) : R = S
open Lean Elab Tactic Meta

/-- `applyEquiv h` closes a goal `R = S` using the private axiom, provided
`h` is a GLOBAL constant (lemma) of type `∀ x, R x ↔ S x`. Local hypotheses
are rejected to enforce the project restriction. -/
elab "applyEquiv " h:ident : tactic => do
  let env ← getEnv
  unless (env.find? h.getId).isSome do
    throwError "applyEquiv: {h.getId} is not a global declaration (local hypotheses not allowed)"
  -- Apply the private axiom with the global constant `h`.
  evalTactic (← `(tactic| apply ruleOfEquiv_ax $(mkIdent h.getId)))



end Classicism
