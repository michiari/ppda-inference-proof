module

public import InferenceProof.PPDA.OperationalPaths

set_option linter.style.header false

/-! # Operational paths in first-step order -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {S : Signature} {E : ExprInterpretation S} {P : Program S}

/-- The first-step presentation of the existing operational trace type. -/
inductive OperationalWalk (E : ExprInterpretation S) (P : Program S) :
    InferenceProof.Configuration S → InferenceProof.Configuration S → Type where
  | nil (c) : OperationalWalk E P c c
  | cons {source middle target} (edge : Σ p : ℚ, Step E P source p middle)
      (rest : OperationalWalk E P middle target) : OperationalWalk E P source target

def OperationalWalk.snoc {source middle target : InferenceProof.Configuration S}
    (walk : OperationalWalk E P source middle) (edge : Σ p : ℚ, Step E P middle p target) :
    OperationalWalk E P source target :=
  match walk with
  | .nil _ => .cons edge (.nil target)
  | .cons first rest => .cons first (rest.snoc edge)

def OperationalPath.prepend {source middle target : InferenceProof.Configuration S}
    (edge : Σ p : ℚ, Step E P source p middle) (path : OperationalPath E P middle target) :
    OperationalPath E P source target :=
  match path with
  | .nil => .snoc .nil edge
  | .snoc previous last => .snoc (prepend edge previous) last

def OperationalWalk.toPath {source target : InferenceProof.Configuration S} :
    OperationalWalk E P source target → OperationalPath E P source target
  | .nil _ => .nil
  | .cons edge rest => rest.toPath.prepend edge

def OperationalWalk.ofPath {source target : InferenceProof.Configuration S} :
    OperationalPath E P source target → OperationalWalk E P source target
  | .nil => .nil source
  | .snoc previous edge => (ofPath previous).snoc edge

theorem OperationalWalk.toPath_snoc {source middle target : InferenceProof.Configuration S}
    (walk : OperationalWalk E P source middle) (edge : Σ p : ℚ, Step E P middle p target) :
    (walk.snoc edge).toPath = .snoc walk.toPath edge := by
  induction walk with
  | nil => rfl
  | cons first rest ih =>
    simp only [snoc, toPath, ih, OperationalPath.prepend]

theorem OperationalWalk.ofPath_prepend {source middle target : InferenceProof.Configuration S}
    (edge : Σ p : ℚ, Step E P source p middle) (path : OperationalPath E P middle target) :
    ofPath (path.prepend edge) = .cons edge (ofPath path) := by
  induction path with
  | nil => rfl
  | snoc previous last ih => simp only [OperationalPath.prepend, ofPath, ih, snoc]

theorem OperationalWalk.toPath_ofPath {source target : InferenceProof.Configuration S}
    (path : OperationalPath E P source target) : (ofPath path).toPath = path := by
  induction path with
  | nil => rfl
  | snoc previous edge ih => simp only [ofPath, toPath_snoc, ih]

theorem OperationalWalk.ofPath_toPath {source target : InferenceProof.Configuration S}
    (walk : OperationalWalk E P source target) : ofPath walk.toPath = walk := by
  induction walk with
  | nil => rfl
  | cons edge rest ih => simp only [toPath, ofPath_prepend, ih]

def operationalWalkEquiv (E : ExprInterpretation S) (P : Program S)
    (source target : InferenceProof.Configuration S) :
    OperationalWalk E P source target ≃ OperationalPath E P source target where
  toFun := OperationalWalk.toPath
  invFun := OperationalWalk.ofPath
  left_inv := OperationalWalk.ofPath_toPath
  right_inv := OperationalWalk.toPath_ofPath

noncomputable def OperationalWalk.weight {source target : InferenceProof.Configuration S} :
    OperationalWalk E P source target → ℝ≥0∞
  | .nil _ => 1
  | .cons edge rest => ENNReal.ofReal (edge.1 : ℝ) * rest.weight

theorem OperationalPath.weight_prepend {source middle target : InferenceProof.Configuration S}
    (edge : Σ p : ℚ, Step E P source p middle) (path : OperationalPath E P middle target) :
    (path.prepend edge).weight = ENNReal.ofReal (edge.1 : ℝ) * path.weight := by
  induction path with
  | nil => simp only [prepend, weight, one_mul, mul_one]
  | snoc previous last ih => simp only [prepend, weight, ih, mul_assoc]

theorem OperationalWalk.weight_toPath {source target : InferenceProof.Configuration S}
    (walk : OperationalWalk E P source target) : walk.toPath.weight = walk.weight := by
  induction walk with
  | nil => rfl
  | cons edge rest ih => simp only [toPath, OperationalPath.weight_prepend, weight, ih]

theorem operational_termination_eq_sum_walk (E : ExprInterpretation S) (P : Program S)
    (source : InferenceProof.Configuration S) (σ : Valuation S) :
    InferenceProof.terminationProbability E P source σ =
      ∑' walk : OperationalWalk E P source ⟨.done, σ, []⟩, walk.weight := by
  rw [operational_termination_eq_sum_path,
    ← (operationalWalkEquiv E P source ⟨.done, σ, []⟩).tsum_eq]
  exact tsum_congr fun walk => walk.weight_toPath

end InferenceProof.PPDA
