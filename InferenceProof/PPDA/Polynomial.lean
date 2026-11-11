module

public import InferenceProof.PPDA.Basic
public import Mathlib.Order.FixedPoints

set_option linter.style.header false

/-!
# The termination polynomial system

The variables are triples `(p, X, q)`, never full-stack configurations. The
quadratic, linear, and constant terms are exactly those in Section 2,
subsection "Termination Probabilities", of `paper/2-background.tex`.
See also `bibliography/esparza/lmcs2004.tex`, Theorem `thm-least-fix`.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

/-- One unknown `[p X | q]` for every pair of controls and one stack symbol. -/
abbrev Summary (Q Γ : Type*) := Q → Γ → Q → ℝ≥0∞

/-- The right-hand side of the pPDA polynomial equations. Coefficients may be
aggregated sums of several rule instances with identical effects.
-/
noncomputable def polynomial
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) (x : Summary Q Γ) : Summary Q Γ :=
  fun p X q =>
    (∑ r, ∑ Y, ∑ Z, ∑ t, weight p X r (.two Y Z) * x r Y t * x t Z q) +
      (∑ r, ∑ Y, weight p X r (.one Y) * x r Y q) + weight p X q .pop

/-- All coefficients are nonnegative, so the termination polynomial is monotone. -/
theorem polynomial_monotone
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) : Monotone (polynomial weight) := by
  intro x y h p X q
  dsimp only [polynomial]
  apply add_le_add _ le_rfl
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro Y _
    apply Finset.sum_le_sum
    intro Z _
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul' (mul_le_mul' le_rfl (h r Y t)) (h t Z q)
  · apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro Y _
    exact mul_le_mul' le_rfl (h r Y q)

/-- The polynomial operator, bundled with its proved monotonicity. -/
noncomputable def polynomialHom
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) : Summary Q Γ →o Summary Q Γ :=
  ⟨polynomial weight, polynomial_monotone weight⟩

/-- The least solution of the summary polynomial equations.
The ambient complete lattice avoids assuming a bound on arbitrary candidate
vectors; the probabilistic bound on the least solution is a separate property.
-/
noncomputable def leastSolution
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) : Summary Q Γ :=
  (polynomialHom weight).lfp

/-- The least solution satisfies the polynomial equations. -/
theorem polynomial_leastSolution
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) :
    polynomial weight (leastSolution weight) = leastSolution weight :=
  (polynomialHom weight).map_lfp

/-- Leastness holds even against pre-fixed candidate vectors. -/
theorem leastSolution_le
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) {x : Summary Q Γ}
    (h : polynomial weight x ≤ x) : leastSolution weight ≤ x :=
  (polynomialHom weight).lfp_le h

/-- The least solution is below every other solution, component by component. -/
theorem leastSolution_le_fixed
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) {x : Summary Q Γ}
    (h : polynomial weight x = x) : leastSolution weight ≤ x :=
  leastSolution_le weight h.le

/-- Termination probabilities obtained from the pPDA's finite quadratic system. -/
noncomputable def Automaton.terminationProbability (A : Automaton Q Γ) : Summary Q Γ :=
  leastSolution A.weight

end InferenceProof.PPDA
