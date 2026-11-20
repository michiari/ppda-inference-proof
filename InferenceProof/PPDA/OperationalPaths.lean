module

public import InferenceProof.OperationalSemantics

set_option linter.style.header false

/-!
# The operational run sum as an edge-product path sum

This file removes the accumulated rational label from the index of `Run`,
without losing derivations or changing their mass. This is one of the bridges
needed to instantiate the generic pPDA first-return theorem for source programs.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof

variable {S : Signature} {E : ExprInterpretation S} {P : Program S}

/-- Every operational transition label is a nonnegative rational. -/
theorem Step.probability_nonnegative {source target : Configuration S} {p : ℚ}
    (step : Step E P source p target) : 0 ≤ p := by
  induction step with
  | rndAssignLeft h _ => exact h.2.1
  | rndAssignRight h _ => exact sub_nonneg.mpr h.2.2
  | seqCont _ _ _ ih => exact ih
  | seqEnd _ ih => exact ih
  | _ => exact zero_le_one

namespace PPDA

/-- An operational trace retains each labelled rule instance, but does not index
the entire path by the product of its labels.
-/
inductive OperationalPath (E : ExprInterpretation S) (P : Program S)
    (source : Configuration S) : Configuration S → Type where
  | nil : OperationalPath E P source source
  | snoc {middle target} (previous : OperationalPath E P source middle)
      (edge : Σ p : ℚ, Step E P middle p target) : OperationalPath E P source target

/-- Recover the accumulated-label run from a trace. -/
def OperationalPath.toRun {source target : Configuration S} :
    OperationalPath E P source target → Σ p : ℚ, Run E P source p target
  | .nil => ⟨1, .refl source⟩
  | .snoc previous edge =>
      let previousRun := previous.toRun
      ⟨previousRun.1 * edge.1, .tail previousRun.2 edge.2⟩

/-- Forget only the accumulated product, keeping all individual transitions. -/
def OperationalPath.ofRun {source target : Configuration S} {p : ℚ} :
    Run E P source p target → OperationalPath E P source target
  | .refl _ => .nil
  | .tail previous step => .snoc (ofRun previous) ⟨_, step⟩

theorem OperationalPath.toRun_ofRun {source target : Configuration S} {p : ℚ}
    (run : Run E P source p target) : (ofRun run).toRun = ⟨p, run⟩ := by
  induction run with
  | refl => rfl
  | @tail middle target a b previous step ih =>
    exact congrArg (fun r : Σ v : ℚ, Run E P source v middle =>
      (⟨r.1 * b, Run.tail r.2 step⟩ : Σ v : ℚ, Run E P source v target)) ih

theorem OperationalPath.ofRun_toRun {source target : Configuration S}
    (path : OperationalPath E P source target) : ofRun path.toRun.2 = path := by
  induction path with
  | nil => rfl
  | snoc previous edge ih => simp only [toRun, ofRun, ih]

/-- Label accumulation neither identifies nor duplicates any rule-labelled paths. -/
def operationalPathRunEquiv (E : ExprInterpretation S) (P : Program S)
    (source target : Configuration S) :
    OperationalPath E P source target ≃ (Σ p : ℚ, Run E P source p target) where
  toFun := OperationalPath.toRun
  invFun run := OperationalPath.ofRun run.2
  left_inv := OperationalPath.ofRun_toRun
  right_inv run := OperationalPath.toRun_ofRun run.2

/-- The product of the individual transition probabilities. -/
noncomputable def OperationalPath.weight {source target : Configuration S} :
    OperationalPath E P source target → ℝ≥0∞
  | .nil => 1
  | .snoc previous edge => previous.weight * ENNReal.ofReal (edge.1 : ℝ)

theorem OperationalPath.weight_eq_label {source target : Configuration S}
    (path : OperationalPath E P source target) :
    path.weight = ENNReal.ofReal (path.toRun.1 : ℝ) := by
  induction path with
  | nil => simp only [weight, toRun, Rat.cast_one, ENNReal.ofReal_one]
  | snoc previous edge ih =>
    have h : 0 ≤ (edge.1 : ℝ) := by exact_mod_cast edge.2.probability_nonnegative
    simp only [weight, toRun, Rat.cast_mul, ENNReal.ofReal_mul' h, ih]

/-- The exact termination definition in `OperationalSemantics.lean` is a sum of
edge-product trace weights. No normalization or semantic equivalence is assumed.
-/
theorem operational_termination_eq_sum_path (E : ExprInterpretation S) (P : Program S)
    (source : Configuration S) (σ : Valuation S) :
    InferenceProof.terminationProbability E P source σ =
      ∑' path : OperationalPath E P source ⟨.done, σ, []⟩, path.weight := by
  unfold InferenceProof.terminationProbability
  rw [← (operationalPathRunEquiv E P source ⟨.done, σ, []⟩).tsum_eq]
  exact tsum_congr fun path => path.weight_eq_label.symm

end PPDA
end InferenceProof
