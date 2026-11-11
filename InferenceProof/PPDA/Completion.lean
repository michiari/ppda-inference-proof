module

public import InferenceProof.PPDA.Polynomial

set_option linter.style.header false

/-! # Completing empty transition rows without changing termination -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

open scoped Classical in
/-- Replace designated empty rows by deterministic head-preserving self-loops. -/
noncomputable def completeWeight (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞)
    (dead : Q → Γ → Prop) : Q → Γ → Q → Replacement Γ → ℝ≥0∞ :=
  fun p X r w => if dead p X then if r = p ∧ w = .one X then 1 else 0 else weight p X r w

open scoped Classical in
theorem polynomial_completeWeight (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞)
    (dead : Q → Γ → Prop) (x : Summary Q Γ) (p : Q) (X : Γ) (q : Q) :
    polynomial (completeWeight weight dead) x p X q =
      if dead p X then x p X q else polynomial weight x p X q := by
  classical
  by_cases h : dead p X <;> simp [polynomial, completeWeight, h, ite_and]

theorem polynomial_zero_row (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞)
    (p : Q) (X : Γ) (h : ∀ r w, weight p X r w = 0) (x : Summary Q Γ) (q : Q) :
    polynomial weight x p X q = 0 := by
  simp only [polynomial, h, zero_mul, Finset.sum_const_zero, zero_add]

/-- Adding a self-loop at an empty row leaves the least solution unchanged.
The proof uses leastness in both directions; arbitrary fixed points need not agree.
-/
theorem leastSolution_completeWeight
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) (dead : Q → Γ → Prop)
    (hdead : ∀ p X, dead p X → ∀ r w, weight p X r w = 0) :
    leastSolution (completeWeight weight dead) = leastSolution weight := by
  classical
  apply le_antisymm
  · apply leastSolution_le
    intro p X q
    rw [polynomial_completeWeight]
    by_cases h : dead p X
    · simp only [h, ite_true, le_refl]
    · simp only [h, ite_false, polynomial_leastSolution, le_refl]
  · apply leastSolution_le
    intro p X q
    by_cases h : dead p X
    · rw [polynomial_zero_row weight p X (hdead p X h)]
      exact bot_le
    · have heq := congrFun (congrFun (congrFun
        (polynomial_leastSolution (completeWeight weight dead)) p) X) q
      rw [polynomial_completeWeight] at heq
      simp only [h, ite_false] at heq
      exact heq.le

end InferenceProof.PPDA
