/-!

# Higher-Order logics

This file defines the basic types and axioms for higher-order logics (HOL).

-/


/-- A type representing propositions.
For easy implementation of built-in tactics, we define a type `t` that is equal to `Prop`.
-/
def t: Type := Prop

/-- A type representing entities.
`opaque` guarantees that no built-in axioms or definitions sneaks into the implementation.
-/
opaque e : Type



namespace Classicism

/-!
 Axioms or inference rules for Classicism.
-/


end Classicism
