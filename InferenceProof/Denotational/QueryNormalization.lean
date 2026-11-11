module

public import InferenceProof.Denotational.FixedPoints
public import InferenceProof.Denotational.Rejection

set_option linter.style.header false

/-! # Recursive queries equal conditioning

Proposition `prop:sq-normalization`, with the appendix's pre-fixed-point proof:
replace beta-star by the normalization of alpha-star, show the resulting pair
is pre-fixed, and use leastness of the simultaneous recursion fixed point.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

theorem sampleQuerySemantics_rejection_fixedPoint (f : FunctionName S) (σ : Valuation S) :
    rejectionFunctional (functionSemantics E P f σ) (sampleQuerySemantics E P f σ) =
      sampleQuerySemantics E P f σ :=
  congrFun (congrFun (congrArg Prod.snd (recursiveEnvironment_fixedPoint E P)) f) σ

/-- Section 5, Proposition `prop:sq-normalization`, including recursive functions. -/
theorem sampleQuerySemantics_eq_normalize (f : FunctionName S) (σ : Valuation S) :
    sampleQuerySemantics E P f σ = normalize (functionSemantics E P f σ) := by
  let env := recursiveEnvironment E P
  let candidate : Environment S := (env.1, fun g state => normalize (env.1 g state))
  have hbeta (g : FunctionName S) (state : Valuation S) :
      normalize (env.1 g state) ≤ env.2 g state :=
    normalize_le_fixedPoint (sampleQuerySemantics_isSubdistribution E P g state)
      (sampleQuerySemantics_rejection_fixedPoint E P g state)
  have hle : candidate ≤ env := ⟨le_rfl, hbeta⟩
  have halpha : (recursionFunctional E P env).1 = env.1 :=
    congrArg Prod.fst (recursiveEnvironment_fixedPoint E P)
  have hpre : recursionFunctional E P candidate ≤ candidate := by
    constructor
    · change (recursionFunctional E P candidate).1 ≤ env.1
      exact ((recursionFunctional_monotone E P) hle).1.trans_eq halpha
    · intro g state outcome
      exact (congrFun (normalize_fixedPoint
        (functionSemantics_isSubdistribution E P g state)) outcome).le
  have hleast := recursiveEnvironment_le E P hpre
  exact le_antisymm (hleast.2 f σ) (hbeta f σ)

@[simp] theorem sampleQuerySemantics_none (f : FunctionName S) (σ : Valuation S) :
    sampleQuerySemantics E P f σ none = 0 := by
  rw [sampleQuerySemantics_eq_normalize, normalize_none]

theorem sampleQuerySemantics_error (f : FunctionName S) :
    sampleQuerySemantics E P f .error = 0 := by
  classical
  rw [sampleQuerySemantics_eq_normalize, functionSemantics_error]
  simp [normalize, dirac]

theorem sampleQuerySemantics_eq_zero_of_certain_rejection (f : FunctionName S)
    (σ : Valuation S) (h : functionSemantics E P f σ none = 1) :
    sampleQuerySemantics E P f σ = 0 := by
  classical
  rw [sampleQuerySemantics_eq_normalize]
  simp only [normalize, h, lt_self_iff_false, ite_false]

theorem queryFromFunction_isSubprobability {K : FunctionKernel S}
    (hK : IsSubprobabilityKernel K) : IsSubprobabilityKernel (queryFromFunction K) :=
  fun σ => normalize_isSubdistribution (hK σ)

end

end InferenceProof.Denotational
