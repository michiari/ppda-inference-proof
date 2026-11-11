module

public import InferenceProof.PPDA.Equivalence
public import InferenceProof.PPDA.Completion

set_option linter.style.header false

/-!
# Completing the finite transition table to a normalized pPDA

An operational head either has total outgoing mass one or has no transitions.
We complete the latter with a deterministic self-loop. Such a loop cannot empty
the stack, and the least polynomial solution is unchanged. This also handles
invalid random-assignment probabilities, whose operational rows are empty.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {S : Signature}

/-- The witnesses stored in an optional enabled transition. -/
abbrev OptionFiber {α : Type*} (o : Option α) := {a : α // o = some a}

noncomputable instance {α : Type*} (o : Option α) : Fintype (OptionFiber o) :=
  Fintype.ofInjective (fun _ => ()) (fun a b _ =>
    Subtype.ext (Option.some.inj (a.2.symm.trans b.2)))

theorem sum_optionFiber {α : Type*} (o : Option α) (f : α → ℚ) :
    (∑ a : OptionFiber o, f a.1) = o.elim 0 f := by
  classical
  cases o with
  | none =>
    have : IsEmpty (OptionFiber (none : Option α)) := ⟨fun a => by cases a.2⟩
    simp
  | some a =>
    let e : OptionFiber (some a) ≃ Unit :=
      ⟨fun _ => (), fun _ => ⟨a, rfl⟩, fun b => Subtype.ext (Option.some.inj b.2),
        fun b => by cases b; rfl⟩
    calc
      _ = ∑ _ : Unit, f a := Fintype.sum_equiv e _ _ fun b => by
        exact congrArg f (Option.some.inj b.2).symm
      _ = _ := by simp

def branchFiberEquiv (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) :
    Branch E P c X ≃ Σ b : Bool, OptionFiber (headMove E P c X b) where
  toFun edge := ⟨edge.choice, edge.move, edge.enabled⟩
  invFun edge := ⟨edge.1, edge.2.1, edge.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_branch_probability (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) :
    (∑ edge : Branch E P c X, edge.move.probability) =
      (headMove E P c X true).elim 0 Move.probability +
        (headMove E P c X false).elim 0 Move.probability := by
  calc
    _ = ∑ edge : Σ b : Bool, OptionFiber (headMove E P c X b), edge.2.1.probability :=
      Fintype.sum_equiv (branchFiberEquiv E P c X) _ _ fun _ => rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp_rw [sum_optionFiber]
      rw [Fintype.sum_bool]

theorem head_probability_zero_or_one (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) :
    let mass := (headMove E P c X true).elim 0 Move.probability +
      (headMove E P c X false).elim 0 Move.probability
    mass = 0 ∨ mass = 1 := by
  classical
  rcases c with ⟨code, state⟩
  cases state with
  | error => cases X <;> simp [headMove, single]
  | normal σ =>
    cases code with
    | done => cases X <;> simp [headMove, single]
    | ret out => cases X <;> simp [headMove, single]
    | endQuery => cases X <;> simp [headMove, single]
    | stmt s => simp [headMove]
    | seq first k =>
      cases first with
      | stmt s =>
        cases s with
        | randomAssign x a n d b =>
          by_cases hv : ValidProbability E σ n d <;> simp [headMove, hv]
        | ite b t e =>
          by_cases hg : (b.eval E σ).val = 0 <;> simp [headMove, single, hg]
        | «while» b body =>
          by_cases hg : (b.eval E σ).val = 0 <;> simp [headMove, single, hg]
        | _ => simp [headMove, single]
      | _ => simp [headMove]

variable (E : ExprInterpretation S) (P : Program S) (C : Stmt S)

noncomputable def rowMass (c : ProgramControl P C) (X : ProgramSymbol P C) : ℚ :=
  ∑ r, ∑ w, programTransition E P C c X r w

theorem rowMass_eq_sum_branch (c : ProgramControl P C) (X : ProgramSymbol P C) :
    rowMass E P C c X = ∑ edge : ProgramBranch E P C c X, edge.move.probability := by
  unfold rowMass programTransition
  calc
    _ = ∑ edge : Σ r, Σ w, ProgramEdge E P C c X r w,
        edge.2.2.1.move.probability := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.sum_sigma]
    _ = _ := Fintype.sum_equiv (programEdgePartition E P C c X) _ _ fun _ => rfl

theorem rowMass_zero_or_one (c : ProgramControl P C) (X : ProgramSymbol P C) :
    rowMass E P C c X = 0 ∨ rowMass E P C c X = 1 := by
  rw [rowMass_eq_sum_branch, sum_branch_probability]
  exact head_probability_zero_or_one E P (rawControl c) X.1

theorem programTransition_zero_of_rowMass (c : ProgramControl P C) (X : ProgramSymbol P C)
    (h : rowMass E P C c X = 0) (r : ProgramControl P C)
    (w : Replacement (ProgramSymbol P C)) : programTransition E P C c X r w = 0 := by
  classical
  apply le_antisymm _ (programTransition_nonnegative E P C c X r w)
  calc
    programTransition E P C c X r w ≤ ∑ v, programTransition E P C c X r v :=
      Finset.single_le_sum (fun v _ => programTransition_nonnegative E P C c X r v)
        (Finset.mem_univ w)
    _ ≤ rowMass E P C c X :=
      Finset.single_le_sum (fun s _ => Finset.sum_nonneg
        (fun v _ => programTransition_nonnegative E P C c X s v)) (Finset.mem_univ r)
    _ = 0 := h

theorem programWeight_zero_of_rowMass (c : ProgramControl P C) (X : ProgramSymbol P C)
    (h : rowMass E P C c X = 0) (r : ProgramControl P C)
    (w : Replacement (ProgramSymbol P C)) : programWeight E P C c X r w = 0 := by
  simp only [programWeight, programTransition_zero_of_rowMass E P C c X h,
    Rat.cast_zero, ENNReal.ofReal_zero]

open scoped Classical in
/-- Dead heads are completed by a deterministic self-loop; live rows are exact. -/
noncomputable def normalizedTransition (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) : ℚ :=
  if rowMass E P C c X = 0 then if r = c ∧ w = .one X then 1 else 0
  else programTransition E P C c X r w

/-- A finite rational pPDA constructed from the source, with normalized rows. -/
noncomputable def programAutomaton : Automaton (ProgramControl P C) (ProgramSymbol P C) where
  transition := normalizedTransition E P C
  nonnegative c X r w := by
    classical
    unfold normalizedTransition
    split_ifs
    · exact zero_le_one
    · exact le_refl 0
    · exact programTransition_nonnegative E P C c X r w
  normalized c X := by
    classical
    by_cases h : rowMass E P C c X = 0
    · simp [normalizedTransition, h, ite_and]
    · simp only [normalizedTransition, h, ite_false]
      exact (rowMass_zero_or_one E P C c X).resolve_left h

theorem programAutomaton_weight :
    (programAutomaton E P C).weight =
      completeWeight (programWeight E P C) (fun c X => rowMass E P C c X = 0) := by
  classical
  funext c X r w
  by_cases hd : rowMass E P C c X = 0
  all_goals by_cases heq : r = c ∧ w = .one X
  all_goals simp [Automaton.weight, programAutomaton, normalizedTransition,
    completeWeight, programWeight, hd, heq]

theorem programAutomaton_leastSolution :
    (programAutomaton E P C).terminationProbability = leastSolution (programWeight E P C) := by
  unfold Automaton.terminationProbability
  rw [programAutomaton_weight]
  exact leastSolution_completeWeight _ _ (programWeight_zero_of_rowMass E P C)

/-- Termination computed by the normalized pPDA's polynomial equations. -/
noncomputable def ppdaTermination (σ₀ σ : Valuation S) : ℝ≥0∞ :=
  (programAutomaton E P C).terminationProbability
    (⟨compile C .done, locations_subset_codeSet P C (compile_mem_locations C .done)⟩, σ₀)
    ⟨.bottom, trivial⟩ (⟨.done, done_mem_codeSet P C⟩, σ)

theorem ppdaTermination_eq_polynomial (σ₀ σ : Valuation S) :
    ppdaTermination E P C σ₀ σ = polynomialTermination E P C σ₀ σ := by
  unfold ppdaTermination polynomialTermination
  rw [programAutomaton_leastSolution]

/-- The pPDA least polynomial solution is the original full-stack termination mass. -/
theorem ppdaTermination_eq_operational (σ₀ σ : Valuation S) :
    ppdaTermination E P C σ₀ σ =
      InferenceProof.terminationProbability E P (initialFragment C σ₀) σ := by
  rw [ppdaTermination_eq_polynomial, polynomialTermination_eq_operational]

/-- Specialization to the whole-program entry convention of Section 4.2. -/
theorem ppdaTermination_eq_programSemantics (σ : Valuation S) :
    ppdaTermination E P (.call P.dummy P.main) (.normal Store.zero) σ =
      InferenceProof.programSemantics E P σ :=
  ppdaTermination_eq_operational E P (.call P.dummy P.main) (.normal Store.zero) σ

end InferenceProof.PPDA
