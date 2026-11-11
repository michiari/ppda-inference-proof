module

public import InferenceProof.PPDA.Equivalence

set_option linter.style.header false

/-!
# Finiteness of the reachable controls and stack alphabet

The sets in Section 4.2 are contained in the finite carriers constructed from
the syntax. Reachability uses positive-probability steps, exactly as in the paper.
The closure argument also applies to zero-probability rule instances.
-/

@[expose] public section

namespace InferenceProof.PPDA

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (C : Stmt S)

/-- The syntactic finite-carrier invariant for a full configuration. -/
def InProgram (source : InferenceProof.Configuration S) : Prop :=
  source.code ∈ codeSet P C ∧
    (∀ X ∈ source.stack, GoodSymbol (codeSet P C) X) ∧ Grounded source.stack

theorem initial_inProgram (σ₀ : Valuation S) :
    InProgram P C (initialFragment C σ₀) := by
  refine ⟨locations_subset_codeSet P C (compile_mem_locations C .done), ?_, .bottom⟩
  simp only [initialFragment, List.mem_singleton]
  rintro X rfl
  trivial

theorem step_inProgram {source target : InferenceProof.Configuration S} {p : ℚ}
    (step : Step E P source p target) (h : InProgram P C source) : InProgram P C target := by
  rcases source with ⟨code, state, stack⟩
  cases stack with
  | nil => exact False.elim (step_source_nonempty E P step rfl)
  | cons X tail =>
    obtain ⟨m, hm, _, ht, hw⟩ := headMove_complete E P (codeSet P C) (code, state)
      X tail (codeSet_closed P C code h.1) step
    have hc := headMove_closed E P C (code, state) X (stepBranch step) m h.1
      (h.2.1 X (by simp)) hm
    refine ⟨?_, ?_, step_grounded step h.2.2⟩
    · have hcode : m.target.1 = target.code := congrArg Prod.fst ht
      simpa only [hcode] using hc.1
    · rw [← hw]
      intro Y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hc.2 Y hy
      · exact h.2.1 Y (List.mem_cons_of_mem X hy)

theorem reachable_inProgram (σ₀ : Valuation S)
    {target : InferenceProof.Configuration S}
    (h : Reachable E P (initialFragment C σ₀) target) : InProgram P C target := by
  induction h with
  | refl => exact initial_inProgram P C σ₀
  | tail _ hstep ih =>
    rcases hstep with ⟨p, _, ⟨step⟩⟩
    exact step_inProgram E P C step ih

/-- Section 4.2's exact set of reachable code/store pairs. -/
def reachableControls (σ₀ : Valuation S) : Set (Control S) :=
  {c | ∃ stack, Reachable E P (initialFragment C σ₀) ⟨c.1, c.2, stack⟩}

/-- Section 4.2's exact stack alphabet: bottom and reachable top symbols. -/
def reachableSymbols (σ₀ : Valuation S) : Set (StackSymbol S) :=
  {X | X = .bottom ∨ ∃ code state tail,
    Reachable E P (initialFragment C σ₀) ⟨code, state, X :: tail⟩}

theorem reachableControls_finite (σ₀ : Valuation S) :
    (reachableControls E P C σ₀).Finite := by
  apply (Set.finite_range (rawControl (U := codeSet P C))).subset
  rintro c ⟨stack, h⟩
  exact ⟨(⟨c.1, (reachable_inProgram E P C σ₀ h).1⟩, c.2), rfl⟩

theorem reachableSymbols_finite (σ₀ : Valuation S) :
    (reachableSymbols E P C σ₀).Finite := by
  apply (Set.finite_range (Subtype.val : ProgramSymbol P C → StackSymbol S)).subset
  rintro X (rfl | ⟨code, state, tail, h⟩)
  · exact ⟨⟨.bottom, trivial⟩, rfl⟩
  · exact ⟨⟨X, (reachable_inProgram E P C σ₀ h).2.1 X (by simp)⟩, rfl⟩

end InferenceProof.PPDA
