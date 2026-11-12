module

public import InferenceProof.Equivalence.Expectation

set_option linter.style.header false

/-! # The call, query, and primitive equations of Section 6 -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (env : Environment S)

def outputReward (x : Var S) (σ : Store S) (r : Valuation S → ℝ≥0∞) :
    Outcome S → ℝ≥0∞
  | some v => r (.normal (σ.update x v))
  | none => r .error

theorem sourceWP_skip (r : Valuation S → ℝ≥0∞) (σ : Valuation S) :
    sourceWP E env .skip r σ = r σ := expect_dirac _ _

theorem sourceWP_assign (x : Var S) (a : Expr S) (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.assign x a) r (.normal σ) = r (.normal (σ.update x (a.eval E σ))) := by
  change expect (Denotational.bind (dirac (Valuation.normal σ)) _) r = _
  rw [bind_dirac, expect_dirac]

theorem sourceWP_observe (r : Valuation S → ℝ≥0∞) (σ : Valuation S) :
    sourceWP E env .observe r σ = r .error := by
  rw [sourceWP, auxiliarySemantics, observe_eq_bind, bind_dirac, expect_dirac]

open scoped Classical in
theorem sourceWP_randomAssign (x : Var S) (a n d b : Expr S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.randomAssign x a n d b) r (.normal σ) =
      if ValidProbability E σ n d then
        ENNReal.ofReal (branchProbability E σ n d : ℝ) *
            r (.normal (σ.update x (a.eval E σ))) +
          ENNReal.ofReal ((1 - branchProbability E σ n d : ℚ) : ℝ) *
            r (.normal (σ.update x (b.eval E σ)))
      else 0 := by
  classical
  change expect (Denotational.bind (dirac (Valuation.normal σ)) _) r = _
  rw [bind_dirac]
  dsimp only
  split_ifs with h
  · change expect ((fun τ => ENNReal.ofReal (branchProbability E σ n d : ℝ) *
        dirac (.normal (σ.update x (a.eval E σ))) τ) +
      (fun τ => ENNReal.ofReal ((1 - branchProbability E σ n d : ℚ) : ℝ) *
        dirac (.normal (σ.update x (b.eval E σ))) τ)) r = _
    rw [expect_add, expect_mul, expect_mul, expect_dirac, expect_dirac]
  · exact expect_zero r

theorem sourceWP_call (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.call x f) r (.normal σ) =
      expect (env.1 f (.normal σ)) (outputReward x σ r) := by
  change expect (Denotational.bind (dirac (Valuation.normal σ)) _) r = _
  rw [bind_dirac, expect_bind]
  congr 1
  funext o
  cases o <;> exact expect_dirac _ _

theorem sourceWP_sampleQuery (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.sampleQuery x f) r (.normal σ) =
      ∑' v, env.2 f (.normal σ) (some v) * r (.normal (σ.update x v)) := by
  change expect (Denotational.bind (dirac (Valuation.normal σ)) _) r = _
  rw [bind_dirac]
  unfold expect
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  congr 1
  funext v
  exact congrArg (fun z => env.2 f (.normal σ) (some v) * z) (expect_dirac _ r)

theorem expect_marginal (out : Var S) (p : StoreMass S) (r : Outcome S → ℝ≥0∞) :
    expect (marginal out p) r = expect p (fun σ => r (read out σ)) := by
  rw [marginal, map, expect_bind]
  simp only [expect_dirac]

theorem expect_option (p : OutputMass S) (r : Outcome S → ℝ≥0∞) :
    expect p r = (∑' v, p (some v) * r (some v)) + p none * r none := by
  have h := totalMass_option (fun o => p o * r o)
  exact h.trans (add_comm _ _)

theorem sourceWP_call_succ (P : Program S) (n : ℕ) (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E (recursionApproximation E P (n + 1)) (.call x f) r (.normal σ) =
      sourceWP E (recursionApproximation E P n) (P.functions f).body
        (fun τ => outputReward x σ r (read (P.functions f).out τ)) (.normal σ) := by
  rw [sourceWP_call, recursionApproximation, Function.iterate_succ_apply']
  change expect (marginal (P.functions f).out
    (auxiliarySemantics E (recursionApproximation E P n) (P.functions f).body
      (dirac (.normal σ)))) _ = _
  rw [expect_marginal]
  rfl

theorem sourceWP_sampleQuery_succ (P : Program S) (n : ℕ) (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E (recursionApproximation E P (n + 1)) (.sampleQuery x f) r (.normal σ) =
      (∑' v, (recursionApproximation E P n).1 f (.normal σ) (some v) *
        r (.normal (σ.update x v))) +
      (recursionApproximation E P n).1 f (.normal σ) none *
        sourceWP E (recursionApproximation E P n) (.sampleQuery x f) r (.normal σ) := by
  rw [sourceWP_sampleQuery, sourceWP_sampleQuery]
  rw [recursionApproximation, Function.iterate_succ_apply']
  change (∑' v, ((recursionApproximation E P n).1 f (.normal σ) (some v) +
    (recursionApproximation E P n).1 f (.normal σ) none *
      (recursionApproximation E P n).2 f (.normal σ) (some v)) *
        r (.normal (σ.update x v))) = _
  simp only [add_mul, mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_left]

theorem sourceWP_call_fixedPoint (P : Program S) (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E (recursiveEnvironment E P) (.call x f) r (.normal σ) =
      sourceWP E (recursiveEnvironment E P) (P.functions f).body
        (fun τ => outputReward x σ r (read (P.functions f).out τ)) (.normal σ) := by
  rw [sourceWP_call]
  conv_lhs => rw [← recursiveEnvironment_fixedPoint E P]
  change expect (marginal (P.functions f).out
    (auxiliarySemantics E (recursiveEnvironment E P) (P.functions f).body
      (dirac (.normal σ)))) _ = _
  rw [expect_marginal]
  rfl

theorem sourceWP_sampleQuery_fixedPoint (P : Program S) (x : Var S) (f : FunctionName S)
    (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E (recursiveEnvironment E P) (.sampleQuery x f) r (.normal σ) =
      (∑' v, (recursiveEnvironment E P).1 f (.normal σ) (some v) *
        r (.normal (σ.update x v))) +
      (recursiveEnvironment E P).1 f (.normal σ) none *
        sourceWP E (recursiveEnvironment E P) (.sampleQuery x f) r (.normal σ) := by
  conv_lhs => rw [sourceWP_sampleQuery, ← recursiveEnvironment_fixedPoint E P]
  rw [sourceWP_sampleQuery]
  change (∑' v, ((recursiveEnvironment E P).1 f (.normal σ) (some v) +
    (recursiveEnvironment E P).1 f (.normal σ) none *
      (recursiveEnvironment E P).2 f (.normal σ) (some v)) *
        r (.normal (σ.update x v))) = _
  simp only [add_mul, mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_left]

end

end InferenceProof.Equivalence
