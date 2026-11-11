module

public import InferenceProof.Denotational.While

set_option linter.style.header false

/-! # Linearity and closure of the auxiliary semantics

Structural induction follows Appendix A, Lemma `lem:sem-linear`. Function and
query parameters may be arbitrary subprobability kernels. The random-assignment
proof also covers the existing semantics' extension of invalid rows by zero.
-/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature}

theorem auxiliarySemantics_massLinear (E : ExprInterpretation S) (env : Environment S)
    (C : Stmt S) : MassLinear (auxiliarySemantics E env C) := by
  induction C with
  | assign => exact assign_massLinear _ _ _
  | randomAssign => exact randomAssign_massLinear _ _ _ _ _ _
  | call => exact functionAssign_massLinear _ _
  | sampleQuery => exact sampleQueryAssign_massLinear _ _
  | skip => exact massLinear_id
  | observe => exact observe_massLinear
  | seq a c iha ihc => exact ihc.comp iha
  | ite b t e iht ihe =>
    exact ((iht.comp (restrict_massLinear E b true)).add
      (ihe.comp (restrict_massLinear E b false))).add errorPart_massLinear
  | «while» b body ih => exact whileSemantics_massLinear E b ih

/-- The matrix space Gamma of Section 5: every row is a subdistribution. -/
def IsSubprobabilityKernel (K : FunctionKernel S) : Prop :=
  ∀ σ, IsSubdistribution (K σ)

def IsSubprobabilityEnvironment (env : Environment S) : Prop :=
  (∀ f, IsSubprobabilityKernel (env.1 f)) ∧ (∀ f, IsSubprobabilityKernel (env.2 f))

def SubprobabilityEnvironment (S : Signature) :=
  {env : Environment S // IsSubprobabilityEnvironment env}

theorem auxiliarySemantics_preserves (E : ExprInterpretation S) (env : Environment S)
    (henv : IsSubprobabilityEnvironment env) (C : Stmt S) :
    PreservesSubdistributions (auxiliarySemantics E env C) := by
  induction C with
  | assign => exact assign_preserves _ _ _
  | randomAssign => exact randomAssign_preserves _ _ _ _ _ _
  | call x f => exact functionAssign_preserves x _ (henv.1 f)
  | sampleQuery x f => exact sampleQueryAssign_preserves x _ (henv.2 f)
  | skip => exact fun _ hp => hp
  | observe => exact observe_preserves
  | seq a c iha ihc => exact preserves_comp ihc iha
  | ite b t e iht ihe =>
    exact branching_preserves E b iht (auxiliarySemantics_massLinear E env t).isLinear
      ihe (auxiliarySemantics_massLinear E env e).isLinear
  | «while» b body ih =>
    exact (whileSemantics_linOp E b ih (auxiliarySemantics_massLinear E env body).isLinear).1

theorem auxiliarySemantics_linOp (E : ExprInterpretation S) (env : Environment S)
    (henv : IsSubprobabilityEnvironment env) (C : Stmt S) :
    PreservesSubdistributions (auxiliarySemantics E env C) ∧
      IsLinear (auxiliarySemantics E env C) :=
  ⟨auxiliarySemantics_preserves E env henv C, (auxiliarySemantics_massLinear E env C).isLinear⟩

theorem restrict_dirac_error (E : ExprInterpretation S) (b : Expr S) (t : Bool) :
    restrict E b t (dirac .error) = 0 := by
  classical
  funext σ
  cases σ <;> simp [restrict, dirac]

theorem errorPart_dirac_error : errorPart (dirac (.error : Valuation S)) = dirac .error := by
  classical
  funext σ
  simp [errorPart, dirac]

/-- The error-store preservation used in Section 5's function-call definition. -/
theorem auxiliarySemantics_error (E : ExprInterpretation S) (env : Environment S)
    (C : Stmt S) : auxiliarySemantics E env C (dirac .error) = dirac .error := by
  induction C with
  | assign => simp only [auxiliarySemantics, assign, bind_dirac]
  | randomAssign => simp only [auxiliarySemantics, randomAssign, bind_dirac]
  | call => simp only [auxiliarySemantics, functionAssign, bind_dirac]
  | sampleQuery => simp only [auxiliarySemantics, sampleQueryAssign, bind_dirac]
  | skip => rfl
  | observe => rw [auxiliarySemantics, observe_eq_bind, bind_dirac]
  | seq a c iha ihc => simpa only [auxiliarySemantics, Function.comp_apply, iha] using ihc
  | ite b t e iht ihe =>
    simp only [auxiliarySemantics, restrict_dirac_error,
      (auxiliarySemantics_massLinear E env t).isLinear.zero,
      (auxiliarySemantics_massLinear E env e).isLinear.zero,
      errorPart_dirac_error, zero_add]
  | «while» b body ih =>
    have hf := congrFun (whileSemantics_fixedPoint E b (auxiliarySemantics E env body))
      (dirac .error)
    simp only [whileFunctional, restrict_dirac_error,
      (auxiliarySemantics_massLinear E env body).isLinear.zero,
      (whileSemantics_massLinear E b (auxiliarySemantics_massLinear E env body)).isLinear.zero,
      errorPart_dirac_error, zero_add] at hf
    exact hf.symm

theorem subprobabilityEnvironment_zero : IsSubprobabilityEnvironment (⊥ : Environment S) :=
  ⟨fun _ _ => isSubdistribution_zero, fun _ _ => isSubdistribution_zero⟩

theorem subprobabilityEnvironment_iSup (env : ℕ → Environment S) (hmono : Monotone env)
    (h : ∀ n, IsSubprobabilityEnvironment (env n)) :
    IsSubprobabilityEnvironment (⨆ n, env n) := by
  constructor
  · intro f σ
    simpa only [Prod.fst_iSup, iSup_apply] using
      isSubdistribution_iSup (fun n => (env n).1 f σ)
        (fun _ _ hn => (hmono hn).1 f σ) (fun n => (h n).1 f σ)
  · intro f σ
    simpa only [Prod.snd_iSup, iSup_apply] using
      isSubdistribution_iSup (fun n => (env n).2 f σ)
        (fun _ _ hn => (hmono hn).2 f σ) (fun n => (h n).2 f σ)

instance : PartialOrder (SubprobabilityEnvironment S) :=
  inferInstanceAs (PartialOrder {env : Environment S // IsSubprobabilityEnvironment env})

instance : OrderBot (SubprobabilityEnvironment S) where
  bot := ⟨⊥, subprobabilityEnvironment_zero⟩
  bot_le env := show (⊥ : Environment S) ≤ env.1 from bot_le

/-- The omega-cpo Gamma^(2n) of Theorem `thm:fixed-point-rec`. -/
instance : OmegaCompletePartialOrder (SubprobabilityEnvironment S) where
  ωSup c := ⟨⨆ n, (c n).1, subprobabilityEnvironment_iSup _
    (fun _ _ h => c.monotone h) (fun n => (c n).2)⟩
  le_ωSup c n := show (c n).1 ≤ ⨆ k, (c k).1 from le_iSup (fun k => (c k).1) n
  ωSup_le c env h := show (⨆ n, (c n).1) ≤ env.1 from iSup_le h

theorem totalMass_rejectionFunctional (q retry : OutputMass S) :
    totalMass (rejectionFunctional q retry) =
      (∑' v, q (some v)) + q none * totalMass retry := by
  change totalMass ((fun o => match o with | some v => q (some v) | none => 0) +
    (fun o => q none * retry o)) = _
  rw [totalMass_add, totalMass_mul, totalMass_option]
  simp only [zero_add]

theorem rejectionFunctional_preserves {q retry : OutputMass S}
    (hq : IsSubdistribution q) (hr : IsSubdistribution retry) :
    IsSubdistribution (rejectionFunctional q retry) := by
  change totalMass _ ≤ 1
  rw [totalMass_rejectionFunctional]
  calc
    _ ≤ (∑' v, q (some v)) + q none * 1 := add_le_add le_rfl (mul_le_mul' le_rfl hr)
    _ = totalMass q := by rw [mul_one, totalMass_option, add_comm]
    _ ≤ 1 := hq

end

end InferenceProof.Denotational
