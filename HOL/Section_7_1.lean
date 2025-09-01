import Mathlib.Tactic
import HOL.Basic

/-!

# Higher-Order logics, Section 5.3: Inductive Definitions

Main results of this section:



-/


namespace Chapter7

-- /- ⊢ p ↔ q, ⊢ p = q -/
-- axiom Tautology_Id : ∀ p : t, (p ↔ True) → (p = True)


-- lemma dubious : ∀ p :t, (p → (p = True)) := by
--   intro p h
--   have h1 : p ↔ True := by
--     constructor
--     · intro h2; exact True.intro
--     · intro h3; exact h
--   exact Tautology_Id p h1


-- lemma P_Imply_P_Id_True : ∀ p : t, (p → p) = True := by
--   intro p
--   apply Tautology_Id
--   constructor
--     · intro h1; exact True.intro
--     · intro h2 h3; exact h3



/-- The operator Z contains all propositional tautologies. -/
def PC (Z : t → t) : t :=
  Z (True)


/-- Z is closed under Modus Ponens -/
def MP (Z : t → t) : t :=
  ∀ p q, (Z p → Z (p → q) → Z q)


/-- Z is closed under the necessitation by operator X. -/
def N (X : t → t) (Z : t → t) : t :=
  ∀ p, (Z p → (Z (X p)))


/-- Z contains the K axiom relative to X. -/
def K (X : t → t) (Z : t → t) : t :=
  Z (MP X)


/-- Z is a K-theory relative to X iff it satisfies PC, MP, N X, K X. -/
def KTheory (X : t → t) (Z : t → t) : t :=
  PC Z ∧ MP Z ∧ N X Z ∧ K X Z


/-- X-necessary at some order. -/
def AtSomeOrder (X : t → t) (q : t) (x : t) : t :=
  ∀ Y : t → t, Y q ∧ (∀ z, Y z → Y (X z)) → Y x
postfix:100 "ˢ" => AtSomeOrder


/-- X-necessary at all orders. -/
def AtAllOrder (X : t → t) (p : t) : t :=
  ∀ x : t, ((Xˢ) p x → x)
postfix:100 "ᵃ" => AtAllOrder


/-- Induction principle for X-necessary at some orders. -/
lemma AtSomeOrder_Induc : ∀ X : t → t, ∀ P : t → t, ∀ q : t, ∀ x : t,
  P q → (∀ a : t, P a → P (X a)) → (Xˢ) q x → P x := by

  intro X P q x hq hind hsome
  unfold AtSomeOrder at hsome
  have hinst := hsome P
  apply hinst
  constructor
  · exact hq
  · exact hind


/-- Elimination principle for X-necessary at all orders. -/
lemma AtAllOrder_Elim : ∀ X : t → t, ∀ r : t, (Xᵃ) r → r := by

  intro X r h
  apply h
  intro Y hY
  exact hY.1


/- Lifting lemma: from (Xᵃ) a derive (Xᵃ) (X a). -/
lemma AtAllOrder_Lift : ∀ X : t → t, ∀ a : t, (Xᵃ) a → (Xᵃ) (X a) := by

  intro X a ha
  -- Need: ∀ x, (Xˢ) (X a) x → x
  intro x hx
  -- Build (Xˢ) a x using hx and then apply ha
  have hSome : (Xˢ) a x := by
    intro Y hY
  -- hY : Y a ∧ ∀ z, Y z → Y (X z)
    have : Y (X a) := hY.2 a hY.1
  -- hx : (Xˢ) (X a) x
    exact hx Y ⟨this, hY.2⟩
  exact ha x hSome


/- Elimination principle for X-necessary at all orders. -/
lemma AtAllOrder_Elim_With_One_X : ∀ X : t → t, ∀ r : t, (Xᵃ) r → X r := by

  intro X r h
  apply AtAllOrder_Lift at h
  apply AtAllOrder_Elim at h
  exact h


/- Elimination principle for X-necessary at all orders. -/
lemma AtAllOrder_Elim_With_Two_X : ∀ X : t → t, ∀ r : t, (Xᵃ) r → X (X r) := by

  intro X r h
  apply AtAllOrder_Lift at h
  apply AtAllOrder_Lift at h
  apply AtAllOrder_Elim at h
  exact h


lemma exercise_7_3a_instance_q : ∀ X : t → t,
  PC (Xᵃ) → K X (Xᵃ) → (∀ p q :t, (Xᵃ) p → ((Xᵃ) (p → q)) → (Xˢ) q q → q):= by

  intro X h1 h2 p q h3 h4 h5
  apply AtAllOrder_Elim at h3
  apply AtAllOrder_Elim at h4
  exact h4 h3


lemma exercise_7_3a_instance_Xq : ∀ X : t → t,

  PC (Xᵃ) → K X (Xᵃ) → (∀ p q :t, (Xᵃ) p → ((Xᵃ) (p → q)) → (Xˢ) q (X q) → X q):= by
  intro X h1 h2 p q h3 h4 h5
  apply AtAllOrder_Elim_With_One_X at h3
  apply AtAllOrder_Elim_With_One_X at h4
  rw [K] at h2
  rw [MP] at h2
  apply AtAllOrder_Elim at h2
  specialize h2 p q
  exact h2 h3 h4


lemma exercise_7_3a_instance_XXq : ∀ X : t → t,
  PC (Xᵃ) → K X (Xᵃ) → (∀ p q :t, (Xᵃ) p → ((Xᵃ) (p → q)) → (Xˢ) q (X (X q)) → X (X q)):= by

  intro X h1 h2 p q h3 h4 h5
  rw [K] at h2
  rw [MP] at h2
  let alpha := (∀ (p q : t), X p → X (p → q) → X q)
  have h6 : X alpha := by
    apply AtAllOrder_Elim_With_One_X at h2
    exact h2
  let beta := (X p → X (p → q) → X q)
  have imp : X (alpha → beta) := by
    sorry
  have h7 : (∀ (p : t) (q : Prop), X p → X (p → q) → X q) := by
    apply AtAllOrder_Elim at h2
    exact h2
  specialize h7 alpha beta h6 imp
  apply AtAllOrder_Elim at h2
  sorry


lemma exercise_7_3a_instance_XXXq : ∀ X : t → t,
  PC (Xᵃ) → K X (Xᵃ) → (∀ p q :t, (Xᵃ) p → ((Xᵃ) (p → q)) → (Xˢ) q (X (X (X q))) → X (X (X q))):= by

  sorry


theorem exercise_7_3a : ∀ X : t → t,
  PC (Xᵃ) → K X (Xᵃ) → MP (Xᵃ) := by

  intro X h1 h2
  rw [PC] at h1
  rw [K] at h2
  rw [MP] at h2
  rw [MP]
  intro p q h3 h4
  rw [AtAllOrder]
  let P := (fun p :t => p) -- Reconsider some proper construction of P.
  have h5 : ∀ x : t, ((Xˢ) q x → P x) := by
    intro x
    have base : P q := by
      sorry
    have ind : (∀ a : t, P a → P (X a)) := by
      sorry
    apply AtSomeOrder_Induc X P q
    · exact base
    · exact ind
  exact h5



end Chapter7
