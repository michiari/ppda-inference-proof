module

public import InferenceProof.Equivalence.RuntimeEquations

set_option linter.style.header false

/-! # Finite loop approximants

The appendix's induction on the number of loop unfoldings, written directly
for Phi iterates, including the error behavior of zero and positive iterates.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (b : Expr S)
    (T : Transformer S) (hT : MassLinear T)

include hT

open scoped Classical in
theorem expect_whileApproximation_succ (n : ℕ) (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    expect (whileApproximation E b T (n + 1) (dirac (.normal σ))) r =
      if (b.eval E σ).val = 0 then r (.normal σ)
      else expect (T (dirac (.normal σ)))
        (fun τ => expect (whileApproximation E b T n (dirac τ)) r) := by
  classical
  have hl := whileApproximation_massLinear E b hT n
  rw [whileApproximation, Function.iterate_succ_apply']
  change expect (whileFunctional E b T (whileApproximation E b T n) (dirac (.normal σ))) r = _
  unfold whileFunctional
  rw [restrict_dirac_normal, restrict_dirac_normal, errorPart_dirac_normal]
  by_cases h : (b.eval E σ).val = 0
  · simp [h, hT.isLinear.zero, hl.isLinear.zero]
  · have hd : decide ((b.eval E σ).val ≠ 0) = true := decide_eq_true h
    simp only [h, hd, Bool.true_eq_false, ite_false, ite_true, zero_add, add_zero]
    rw [hl, expect_bind]

theorem expect_whileApproximation_error (n : ℕ) (r : Valuation S → ℝ≥0∞) :
    expect (whileApproximation E b T (n + 1) (dirac .error)) r = r .error := by
  rw [whileApproximation, Function.iterate_succ_apply']
  change expect (whileFunctional E b T (whileApproximation E b T n) (dirac .error)) r = _
  unfold whileFunctional
  rw [restrict_dirac_error, restrict_dirac_error, errorPart_dirac_error,
    hT.isLinear.zero, (whileApproximation_massLinear E b hT n).isLinear.zero]
  simp only [zero_add, expect_dirac]

end

end InferenceProof.Equivalence
