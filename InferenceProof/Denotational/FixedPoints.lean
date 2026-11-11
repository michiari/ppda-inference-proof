module

public import InferenceProof.Denotational.Continuity

set_option linter.style.header false

/-! # The simultaneous recursion fixed point and well-defined semantics

Theorem `thm:fixed-point-rec` of Section 5. The proof follows the paper:
Gamma^(2n) is an omega-cpo, Psi preserves its rows, the auxiliary semantics
and affine rejection clause are continuous, and Kleene iteration gives the
least fixed point. Closure of every full statement follows by structural induction.
-/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

theorem recursionFunctional_omegaContinuous : ChainContinuous (recursionFunctional E P) := by
  apply ChainContinuous.prodMk
  · apply ChainContinuous.of_apply₂
    intro f
    exact (functionFromBody_omegaContinuous (P.functions f).out).comp
      (auxiliarySemantics_omegaContinuous E (P.functions f).body)
  · apply ChainContinuous.of_apply₂
    intro f
    apply ChainContinuous.of_apply₂
    intro σ
    have ha : ChainContinuous (fun env : Environment S => env.1 f σ) :=
      ((ChainContinuous.fst.apply₂ f).apply₂ σ)
    have hb : ChainContinuous (fun env : Environment S => env.2 f σ) :=
      ((ChainContinuous.snd.apply₂ f).apply₂ σ)
    apply ChainContinuous.of_apply₂
    intro outcome
    cases outcome with
    | none =>
      change ChainContinuous (fun env : Environment S =>
        0 + env.1 f σ none * env.2 f σ none)
      exact omegaContinuous_add ChainContinuous.const
        (omegaContinuous_mul (ha.apply₂ none) (hb.apply₂ none))
    | some v =>
      change ChainContinuous (fun env : Environment S =>
        env.1 f σ (some v) + env.1 f σ none * env.2 f σ (some v))
      exact omegaContinuous_add (ha.apply₂ (some v))
        (omegaContinuous_mul (ha.apply₂ none) (hb.apply₂ (some v)))

theorem recursionFunctional_monotone : Monotone (recursionFunctional E P) :=
  (recursionFunctional_omegaContinuous E P).monotone

theorem recursionFunctional_iSup (env : ℕ → Environment S) (h : Monotone env) :
    recursionFunctional E P (⨆ n, env n) = ⨆ n, recursionFunctional E P (env n) :=
  omegaContinuous_iSup (recursionFunctional_omegaContinuous E P) env h

theorem recursionFunctional_preserves {env : Environment S}
    (h : IsSubprobabilityEnvironment env) :
    IsSubprobabilityEnvironment (recursionFunctional E P env) := by
  constructor
  · intro f σ
    exact (auxiliarySemantics_preserves E env h (P.functions f).body (dirac σ)
      (isSubdistribution_dirac σ)).map (read (P.functions f).out)
  · intro f σ
    exact rejectionFunctional_preserves (h.1 f σ) (h.2 f σ)

theorem recursionApproximation_monotone : Monotone (recursionApproximation E P) :=
  (recursionFunctional_monotone E P).monotone_iterate_of_le_map bot_le

theorem recursionApproximation_subprobability (n : ℕ) :
    IsSubprobabilityEnvironment (recursionApproximation E P n) := by
  induction n with
  | zero => exact subprobabilityEnvironment_zero
  | succ n ih =>
    rw [recursionApproximation, Function.iterate_succ_apply']
    exact recursionFunctional_preserves E P ih

theorem recursiveEnvironment_subprobability :
    IsSubprobabilityEnvironment (recursiveEnvironment E P) :=
  subprobabilityEnvironment_iSup _ (recursionApproximation_monotone E P)
    (recursionApproximation_subprobability E P)

theorem recursiveEnvironment_fixedPoint :
    recursionFunctional E P (recursiveEnvironment E P) = recursiveEnvironment E P :=
  kleene_fixedPoint _ (recursionFunctional_omegaContinuous E P)

/-- Leastness holds against every pre-fixed environment in the ambient lattice. -/
theorem recursiveEnvironment_le {env : Environment S}
    (h : recursionFunctional E P env ≤ env) : recursiveEnvironment E P ≤ env :=
  kleene_le (recursionFunctional_monotone E P) h

/-- Psi on exactly Gamma^(2n), the paper's subprobability-kernel space. -/
def recursionOperator (env : SubprobabilityEnvironment S) : SubprobabilityEnvironment S :=
  ⟨recursionFunctional E P env.1, recursionFunctional_preserves E P env.2⟩

def recursionFixedPoint : SubprobabilityEnvironment S :=
  ⟨recursiveEnvironment E P, recursiveEnvironment_subprobability E P⟩

theorem recursionOperator_omegaContinuous : ChainContinuous (recursionOperator E P) := by
  apply ωScottContinuous.of_monotone_map_ωSup
  refine ⟨fun env env' h => recursionFunctional_monotone E P h, ?_⟩
  intro c
  apply Subtype.ext
  change recursionFunctional E P (⨆ n, (c n).1) =
    ⨆ n, recursionFunctional E P (c n).1
  exact recursionFunctional_iSup E P _ (fun _ _ h => c.monotone h)

/-- Section 5, Theorem `thm:fixed-point-rec`, on the intended domain. -/
theorem recursionFixedPoint_isLeast :
    IsLeast (Function.fixedPoints (recursionOperator E P)) (recursionFixedPoint E P) := by
  refine ⟨Subtype.ext (recursiveEnvironment_fixedPoint E P), ?_⟩
  intro env h
  exact recursiveEnvironment_le E P
    (congrArg Subtype.val (show recursionOperator E P env = env from h)).le

/-- Appendix A, Lemma `lem:sem-linear`, together with subdistribution closure. -/
theorem semantics_linOp (C : Stmt S) :
    PreservesSubdistributions (semantics E P C) ∧ IsLinear (semantics E P C) :=
  auxiliarySemantics_linOp E _ (recursiveEnvironment_subprobability E P) C

theorem semantics_massLinear (C : Stmt S) : MassLinear (semantics E P C) :=
  auxiliarySemantics_massLinear E _ C

theorem semantics_error (C : Stmt S) : semantics E P C (dirac .error) = dirac .error :=
  auxiliarySemantics_error E _ C

theorem functionSemantics_error (f : FunctionName S) :
    functionSemantics E P f .error = dirac none := by
  have h := congrFun (congrFun (congrArg Prod.fst (recursiveEnvironment_fixedPoint E P)) f)
    .error
  change marginal (P.functions f).out
    (auxiliarySemantics E (recursiveEnvironment E P) (P.functions f).body (dirac .error)) =
      functionSemantics E P f .error at h
  rw [auxiliarySemantics_error, marginal, map, bind_dirac] at h
  exact h.symm

theorem fragmentSemantics_isSubdistribution (C : Stmt S) (σ : Valuation S) :
    IsSubdistribution (fragmentSemantics E P C σ) :=
  (semantics_linOp E P C).1 (dirac σ) (isSubdistribution_dirac σ)

theorem programSemantics_isSubdistribution : IsSubdistribution (programSemantics E P) :=
  fragmentSemantics_isSubdistribution E P _ _

theorem queryProgramSemantics_isSubdistribution : IsSubdistribution (queryProgramSemantics E P) :=
  fragmentSemantics_isSubdistribution E P _ _

theorem functionSemantics_isSubdistribution (f : FunctionName S) (σ : Valuation S) :
    IsSubdistribution (functionSemantics E P f σ) :=
  (recursiveEnvironment_subprobability E P).1 f σ

theorem sampleQuerySemantics_isSubdistribution (f : FunctionName S) (σ : Valuation S) :
    IsSubdistribution (sampleQuerySemantics E P f σ) :=
  (recursiveEnvironment_subprobability E P).2 f σ

/-- Theorem `thm:fixed-point-while` applied to every actual semantic body. -/
theorem semantics_while_isLeast (b : Expr S) (body : Stmt S) :
    IsLeast (Function.fixedPoints (whileOperator E b
      ⟨semantics E P body, semantics_linOp E P body⟩))
      (whileFixedPoint E b ⟨semantics E P body, semantics_linOp E P body⟩) :=
  whileFixedPoint_isLeast E b _

end

end InferenceProof.Denotational
