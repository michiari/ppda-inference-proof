module

public import InferenceProof.Denotational

set_option linter.style.header false

/-! # Weighted continuations and the structural denotational equations

The weighted sums here express the concatenation of terminating runs used in
the appendix's sequencing argument. Rewards need not be bounded.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open Denotational

noncomputable section

variable {α β : Type*} {S : Signature}

def expect (p : Mass α) (r : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * r a

@[simp] theorem expect_dirac (a : α) (r : α → ℝ≥0∞) : expect (dirac a) r = r a := by
  classical
  simp [expect, dirac]

@[simp] theorem expect_zero (r : α → ℝ≥0∞) : expect 0 r = 0 := by
  simp [expect]

theorem expect_mono {p q : Mass α} {r s : α → ℝ≥0∞} (hp : p ≤ q) (hr : r ≤ s) :
    expect p r ≤ expect q s :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul' (hp a) (hr a)

theorem expect_bind (p : Mass α) (K : α → Mass β) (r : β → ℝ≥0∞) :
    expect (bind p K) r = expect p (fun a => expect (K a) r) := by
  simp only [expect, Denotational.bind, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right, mul_assoc]
  exact ENNReal.tsum_comm

theorem expect_add (p q : Mass α) (r : α → ℝ≥0∞) :
    expect (p + q) r = expect p r + expect q r := by
  simp only [expect, Pi.add_apply, add_mul, ENNReal.tsum_add]

theorem expect_mul (c : ℝ≥0∞) (p : Mass α) (r : α → ℝ≥0∞) :
    expect (fun a => c * p a) r = c * expect p r := by
  simp only [expect, mul_assoc, ENNReal.tsum_mul_left]

theorem expect_iSup (p : ℕ → Mass α) (hp : Monotone p) (r : α → ℝ≥0∞) :
    expect (⨆ n, p n) r = ⨆ n, expect (p n) r := by
  simp only [expect, iSup_apply, ENNReal.iSup_mul]
  exact tsum_iSup_of_monotone _ (fun i j hij a => mul_le_mul' (hp hij a) le_rfl)

/-- The normal continuation and the separate error continuation. -/
def reward (K : Store S → ℝ≥0∞) (e : ℝ≥0∞) : Valuation S → ℝ≥0∞
  | .normal σ => K σ
  | .error => e

def sourceWP (E : ExprInterpretation S) (env : Environment S) (C : Stmt S)
    (r : Valuation S → ℝ≥0∞) (σ : Valuation S) : ℝ≥0∞ :=
  expect (auxiliarySemantics E env C (dirac σ)) r

theorem sourceWP_error (E : ExprInterpretation S) (env : Environment S) (C : Stmt S)
    (r : Valuation S → ℝ≥0∞) : sourceWP E env C r .error = r .error := by
  rw [sourceWP, auxiliarySemantics_error, expect_dirac]

theorem sourceWP_mono (E : ExprInterpretation S) (env : Environment S) (C : Stmt S)
    {r s : Valuation S → ℝ≥0∞} (h : r ≤ s) : sourceWP E env C r ≤ sourceWP E env C s :=
  fun _ => expect_mono le_rfl h

theorem sourceWP_seq (E : ExprInterpretation S) (env : Environment S) (a b : Stmt S)
    (r : Valuation S → ℝ≥0∞) (σ : Valuation S) :
    sourceWP E env (.seq a b) r σ = sourceWP E env a (sourceWP E env b r) σ := by
  change expect (auxiliarySemantics E env b (auxiliarySemantics E env a (dirac σ))) r = _
  rw [auxiliarySemantics_massLinear E env b, expect_bind]
  rfl

theorem restrict_dirac_normal (E : ExprInterpretation S) (b : Expr S) (t : Bool)
    (σ : Store S) : restrict E b t (dirac (.normal σ)) =
      if decide ((b.eval E σ).val ≠ 0) = t then dirac (.normal σ) else 0 := by
  classical
  by_cases h : decide ((b.eval E σ).val ≠ 0) = t
  · rw [ite_eq_left h]
    funext τ
    cases τ with
    | error => simp only [restrict, dirac, reduceCtorEq, ite_false]
    | normal τ =>
      by_cases heq : σ = τ
      · subst τ; simp only [restrict, h, ite_true]
      · simp only [restrict, dirac, Valuation.normal.injEq, heq, ite_false, ite_self]
  · rw [ite_eq_right h]
    funext τ
    cases τ with
    | error => rfl
    | normal τ =>
      by_cases heq : σ = τ
      · subst τ; simp only [restrict, h, ite_false, Pi.zero_apply]
      · simp only [restrict, dirac, Valuation.normal.injEq, heq, ite_false,
          ite_self, Pi.zero_apply]

@[simp] theorem errorPart_dirac_normal (σ : Store S) : errorPart (dirac (.normal σ)) = 0 := by
  classical
  funext τ
  simp [errorPart, dirac]

theorem sourceWP_ite (E : ExprInterpretation S) (env : Environment S)
    (b : Expr S) (t f : Stmt S) (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.ite b t f) r (.normal σ) =
      if (b.eval E σ).val = 0 then sourceWP E env f r (.normal σ)
      else sourceWP E env t r (.normal σ) := by
  classical
  change expect (auxiliarySemantics E env t (restrict E b true (dirac (.normal σ))) +
    auxiliarySemantics E env f (restrict E b false (dirac (.normal σ))) +
    errorPart (dirac (.normal σ))) r = _
  rw [restrict_dirac_normal, restrict_dirac_normal, errorPart_dirac_normal]
  by_cases h : (b.eval E σ).val = 0 <;>
    simp [sourceWP, h, (auxiliarySemantics_massLinear E env t).isLinear.zero,
      (auxiliarySemantics_massLinear E env f).isLinear.zero]

theorem sourceWP_while (E : ExprInterpretation S) (env : Environment S)
    (b : Expr S) (body : Stmt S) (r : Valuation S → ℝ≥0∞) (σ : Store S) :
    sourceWP E env (.while b body) r (.normal σ) =
      if (b.eval E σ).val = 0 then r (.normal σ)
      else sourceWP E env body (sourceWP E env (.while b body) r) (.normal σ) := by
  classical
  have hl := whileSemantics_massLinear E b (auxiliarySemantics_massLinear E env body)
  change expect (whileSemantics E b (auxiliarySemantics E env body) (dirac (.normal σ))) r = _
  rw [← whileSemantics_fixedPoint E b (auxiliarySemantics E env body)]
  unfold whileFunctional
  rw [restrict_dirac_normal, restrict_dirac_normal, errorPart_dirac_normal]
  by_cases h : (b.eval E σ).val = 0
  · simp [h, (auxiliarySemantics_massLinear E env body).isLinear.zero,
      hl.isLinear.zero]
  · have hd : decide ((b.eval E σ).val ≠ 0) = true := decide_eq_true h
    simp only [h, hd, ite_false, Bool.true_eq_false, ite_true, zero_add, add_zero]
    rw [hl, expect_bind]
    rfl

end

end InferenceProof.Equivalence
