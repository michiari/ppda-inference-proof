module

public import InferenceProof.Equivalence.Operational

set_option linter.style.header false

/-! # The runtime first-step equations

The head evaluator already proved equivalent to individual operational rules
is used to write the continuation equations of the diagrams in Section 6.
The value defined here is proved equal to the original run sum, rather than
being an alternative definition of operational semantics.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

def moveTarget (m : Move S) (tail : List (StackSymbol S)) : Configuration S :=
  ⟨m.target.1, m.target.2, m.replacement.word ++ tail⟩

theorem sum_branches (c : Control S) (X : StackSymbol S) (F : Move S → ℝ≥0∞) :
    (∑' b : Branch E P c X, F b.move) =
      ∑ b : Bool, (headMove E P c X b).elim 0 F := by
  classical
  let e : Branch E P c X ≃ Σ b : Bool, {m // headMove E P c X b = some m} :=
    { toFun := fun b => ⟨b.choice, b.move, b.enabled⟩
      invFun := fun b => ⟨b.1, b.2.1, b.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.tsum_eq, ENNReal.tsum_sigma']
  rw [← tsum_fintype (L := SummationFilter.unconditional Bool)
    (fun b : Bool => (headMove E P c X b).elim 0 F)]
  apply tsum_congr
  intro b
  change (∑' m : {m // headMove E P c X b = some m}, F m.1) = _
  cases h : headMove E P c X b with
  | none =>
    simp only [Option.elim_none]
    have hz : (fun z : {m : Move S // (none : Option (Move S)) = some m} => F z.1) =
        fun _ => 0 := by funext z; cases z.2
    rw [hz, tsum_zero]
  | some m =>
    simp only [Option.elim_some]
    apply tsum_eq_single (f := fun z : {z : Move S // some m = some z} => F z.1) ⟨m, rfl⟩
    intro z hz
    exact False.elim (hz (Subtype.ext (Option.some.inj z.2).symm))

open scoped Classical in
def headFunctional (σ : Valuation S) (V : Configuration S → ℝ≥0∞)
    (c : Configuration S) : ℝ≥0∞ :=
  match c.stack with
  | [] => dirac ⟨.done, σ, []⟩ c
  | X :: tail => if Boundary X tail then
      ∑' b : Branch E P (c.code, c.store) X,
        ENNReal.ofReal (b.move.probability : ℝ) * V (moveTarget b.move tail)
    else 0

theorem headFunctional_monotone (σ : Valuation S) : Monotone (headFunctional E P σ) := by
  classical
  intro V W h c
  cases hs : c.stack with
  | nil => simp only [headFunctional, hs]; exact le_rfl
  | cons X tail =>
    simp only [headFunctional, hs]
    split_ifs
    · exact ENNReal.tsum_le_tsum fun b => mul_le_mul' le_rfl (h _)
    · rfl

theorem headFunctional_omegaContinuous (σ : Valuation S) :
    ChainContinuous (headFunctional E P σ) := by
  classical
  apply ChainContinuous.of_apply₂
  intro c
  cases hs : c.stack with
  | nil => simp only [headFunctional, hs]; exact ChainContinuous.const
  | cons X tail =>
    simp only [headFunctional, hs]
    split_ifs
    · apply omegaContinuous_tsum
      intro b
      exact omegaContinuous_mul ChainContinuous.const (ChainContinuous.apply _)
    · exact ChainContinuous.const

def runtimeValue (σ : Valuation S) : Configuration S → ℝ≥0∞ :=
  ⨆ n : ℕ, (headFunctional E P σ)^[n] ⊥

theorem runtimeValue_fixedPoint (σ : Valuation S) :
    headFunctional E P σ (runtimeValue E P σ) = runtimeValue E P σ :=
  kleene_fixedPoint _ (headFunctional_omegaContinuous E P σ)

theorem runtimeValue_le (σ : Valuation S) {V : Configuration S → ℝ≥0∞}
    (h : headFunctional E P σ V ≤ V) : runtimeValue E P σ ≤ V :=
  kleene_le (headFunctional_monotone E P σ) h

def branchToEdge (c : Control S) (X : StackSymbol S) (tail : List (StackSymbol S))
    (hb : Boundary X tail) (b : Branch E P c X) :
    FullEdge E P ⟨c.1, c.2, X :: tail⟩ :=
  ⟨b.move.probability, moveTarget b.move tail,
    headMove_step E P c X b.choice b.move b.enabled tail hb⟩

theorem branchToEdge_branch (c : Control S) (X : StackSymbol S) (tail : List (StackSymbol S))
    (hb : Boundary X tail) (b : Branch E P c X) :
    stepBranch (branchToEdge E P c X tail hb b).2.2 = b.choice :=
  headMove_step_branch E P c X b.choice b.move b.enabled tail hb

def branchEdgeEquiv (U : Finset (Code S)) (c : Control S)
    (X : StackSymbol S) (tail : List (StackSymbol S))
    (hc : LocalClosed U c.1) (hb : Boundary X tail) :
    Branch E P c X ≃ FullEdge E P ⟨c.1, c.2, X :: tail⟩ := by
  apply Equiv.ofBijective (branchToEdge E P c X tail hb)
  constructor
  · intro a b h
    apply Branch.ext
    simpa only [branchToEdge_branch] using congrArg (fun e => stepBranch e.2.2) h
  · rintro ⟨p, target, step⟩
    obtain ⟨m, hm, _, _, _⟩ := headMove_complete E P U c X tail hc step
    refine ⟨⟨stepBranch step, m, hm⟩, ?_⟩
    apply fullEdge_ext E P U c X tail hc
    exact branchToEdge_branch E P c X tail hb _

theorem operationalFunctional_eq_headFunctional (C : Stmt S) (σ : Valuation S)
    (V : Configuration S → ℝ≥0∞) (c : Configuration S) (hc : InProgram P C c) :
    operationalFunctional E P σ V c = headFunctional E P σ V c := by
  classical
  rcases c with ⟨code, state, stack⟩
  cases stack with
  | nil =>
    have : IsEmpty (FullEdge E P ⟨code, state, []⟩) :=
      ⟨fun e => step_source_nonempty E P e.2.2 rfl⟩
    simp [operationalFunctional, headFunctional]
  | cons X tail =>
    have hb := hc.2.2.boundary
    simp only [operationalFunctional, headFunctional, hb, ite_true]
    have hne : (⟨.done, σ, []⟩ : Configuration S) ≠ ⟨code, state, X :: tail⟩ :=
      by
        intro h
        have hs := congrArg Configuration.stack h
        cases hs
    rw [dirac, ite_eq_right hne, zero_add,
      ← (branchEdgeEquiv E P (codeSet P C) (code, state) X tail
        (codeSet_closed P C _ hc.1) hb).tsum_eq]
    rfl

theorem runtime_iterate_eq_bounded (C : Stmt S) (σ : Valuation S) (n : ℕ)
    (c : Configuration S) (hc : InProgram P C c) :
    (headFunctional E P σ)^[n] ⊥ c = boundedRunSum E P σ n c := by
  induction n generalizing c with
  | zero => rw [boundedRunSum_zero]; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', boundedRunSum_succ,
      ← operationalFunctional_eq_headFunctional E P C σ _ c hc]
    unfold operationalFunctional
    congr 1
    apply tsum_congr
    intro e
    rw [ih e.2.1 (step_inProgram E P C e.2.2 hc)]

theorem runtimeValue_eq_terminationProbability (C : Stmt S) (σ : Valuation S)
    (c : Configuration S) (hc : InProgram P C c) :
    runtimeValue E P σ c = InferenceProof.terminationProbability E P c σ := by
  change runtimeValue E P σ c = (fun z => InferenceProof.terminationProbability E P z σ) c
  rw [terminationProbability_eq_iSup]
  simp only [runtimeValue, iSup_apply]
  exact iSup_congr fun n => runtime_iterate_eq_bounded E P C σ n c hc

end

end InferenceProof.Equivalence
