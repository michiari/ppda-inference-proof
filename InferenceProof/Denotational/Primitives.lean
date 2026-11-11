module

public import InferenceProof.Denotational.Linear

set_option linter.style.header false

/-! # Subdistribution and linearity properties of primitive statements -/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature}

theorem totalMass_mono {α : Type*} {p q : Mass α} (h : p ≤ q) :
    totalMass p ≤ totalMass q := ENNReal.tsum_le_tsum h

theorem IsSubdistribution.mono {α : Type*} {p q : Mass α}
    (hq : IsSubdistribution q) (h : p ≤ q) : IsSubdistribution p :=
  (totalMass_mono h).trans hq

theorem restrict_le (E : ExprInterpretation S) (b : Expr S) (t : Bool) (p : StoreMass S) :
    restrict E b t p ≤ p := by
  intro σ
  cases σ with
  | error => exact bot_le
  | normal σ => dsimp only [restrict]; split_ifs <;> first | exact le_rfl | exact bot_le

theorem restrict_preserves (E : ExprInterpretation S) (b : Expr S) (t : Bool) :
    PreservesSubdistributions (restrict E b t) :=
  fun p hp => hp.mono (restrict_le E b t p)

theorem restrict_massLinear (E : ExprInterpretation S) (b : Expr S) (t : Bool) :
    MassLinear (restrict E b t) := by
  classical
  intro p
  funext σ
  cases σ with
  | error => simp [restrict, bind]
  | normal σ =>
    by_cases h : decide ((b.eval E σ).val ≠ 0) = t
    all_goals simp only [restrict, bind, h, ite_true, ite_false, dirac, mul_ite,
      mul_one, mul_zero, tsum_ite_eq, tsum_zero]

theorem errorPart_massLinear : MassLinear (errorPart (S := S)) := by
  classical
  intro p
  funext σ
  cases σ <;> simp [errorPart, bind, dirac]

/-- The guard branches and error input form a partition of the entire mass. -/
theorem restrict_partition (E : ExprInterpretation S) (b : Expr S) (p : StoreMass S) :
    restrict E b false p + restrict E b true p + errorPart p = p := by
  classical
  funext σ
  cases σ with
  | error => simp [restrict, errorPart, dirac]
  | normal σ =>
    by_cases h : (b.eval E σ).val = 0
    all_goals simp [restrict, errorPart, dirac, h]

theorem assign_massLinear (E : ExprInterpretation S) (x : Var S) (e : Expr S) :
    MassLinear (assign E x e) := massLinear_bind _

theorem assign_preserves (E : ExprInterpretation S) (x : Var S) (e : Expr S) :
    PreservesSubdistributions (assign E x e) := by
  intro p hp
  apply hp.bind
  intro σ
  cases σ <;> exact isSubdistribution_dirac _

theorem randomAssign_massLinear (E : ExprInterpretation S) (x : Var S)
    (a n d b : Expr S) : MassLinear (randomAssign E x a n d b) := massLinear_bind _

theorem randomAssign_preserves (E : ExprInterpretation S) (x : Var S)
    (a n d b : Expr S) : PreservesSubdistributions (randomAssign E x a n d b) := by
  classical
  intro p hp
  apply hp.bind
  intro σ
  cases σ with
  | error => exact isSubdistribution_dirac _
  | normal σ =>
    by_cases hv : ValidProbability E σ n d
    · simp only [hv, ite_true]
      change totalMass ((fun σ' => _ * dirac _ σ') + (fun σ' => _ * dirac _ σ')) ≤ 1
      rw [totalMass_add, totalMass_mul, totalMass_mul, totalMass_dirac, totalMass_dirac,
        mul_one, mul_one]
      rw [← ENNReal.ofReal_add (Rat.cast_nonneg.mpr hv.2.1)
        (Rat.cast_nonneg.mpr (sub_nonneg.mpr hv.2.2)), ← Rat.cast_add,
        add_sub_cancel, Rat.cast_one, ENNReal.ofReal_one]
    · simp only [hv, ite_false]
      exact isSubdistribution_zero

theorem observe_eq_bind (p : StoreMass S) :
    observe p = bind p (fun _ => dirac .error) := by
  funext σ
  exact ENNReal.tsum_mul_right.symm

theorem observe_massLinear : MassLinear (observe (S := S)) := by
  intro p
  rw [observe_eq_bind]
  simp only [observe_eq_bind, bind_dirac]

theorem observe_preserves : PreservesSubdistributions (observe (S := S)) := by
  intro p hp
  rw [observe_eq_bind]
  exact hp.bind (fun _ => isSubdistribution_dirac _)

theorem functionAssign_massLinear (x : Var S) (K : FunctionKernel S) :
    MassLinear (functionAssign x K) := massLinear_bind _

theorem functionAssign_preserves (x : Var S) (K : FunctionKernel S)
    (hK : ∀ σ, IsSubdistribution (K σ)) : PreservesSubdistributions (functionAssign x K) := by
  intro p hp
  apply hp.bind
  intro σ
  cases σ with
  | error => exact isSubdistribution_dirac _
  | normal σ =>
    apply (hK (.normal σ)).bind
    intro outcome
    cases outcome <;> exact isSubdistribution_dirac _

theorem sampleQueryAssign_massLinear (x : Var S) (K : FunctionKernel S) :
    MassLinear (sampleQueryAssign x K) := massLinear_bind _

theorem totalMass_option {α : Type*} [Finite α] (p : Mass (Option α)) :
    totalMass p = p none + ∑' a, p (some a) := by
  let _ := Fintype.ofFinite α
  simp only [totalMass, tsum_fintype, Fintype.sum_option]

theorem sampleQueryAssign_preserves (x : Var S) (K : FunctionKernel S)
    (hK : ∀ σ, IsSubdistribution (K σ)) :
    PreservesSubdistributions (sampleQueryAssign x K) := by
  intro p hp
  apply hp.bind
  intro σ
  cases σ with
  | error => exact isSubdistribution_dirac _
  | normal σ =>
    change totalMass (bind (fun v => K (.normal σ) (some v))
      (fun v => dirac (Valuation.normal (σ.update x v)))) ≤ 1
    rw [totalMass_bind]
    simp only [totalMass_dirac, mul_one]
    calc
      _ ≤ K (.normal σ) none + ∑' v, K (.normal σ) (some v) := le_add_left le_rfl
      _ = totalMass (K (.normal σ)) := (totalMass_option _).symm
      _ ≤ 1 := hK (.normal σ)

end

end InferenceProof.Denotational
