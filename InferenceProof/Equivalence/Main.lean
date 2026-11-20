module

public import InferenceProof.Equivalence.Soundness
public import InferenceProof.Equivalence.Recursion

set_option linter.style.header false

/-! # Equivalence of denotational and operational semantics

Section 6, Theorem `thm:equivalence`, and its appendix theorem. The theorem
compares source denotations with the sum over rationally labelled operational
runs. The statement has no simulation or fixed-point
hypotheses, and applies to every source fragment and initial valuation.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

theorem expect_point (p : Mass (Valuation S)) (o : Valuation S) :
    expect p (fun σ => dirac σ o) = p o :=
  congrFun (bind_dirac_right p) o

theorem runtimeDenotation_initial (C : Stmt S) (σ o : Valuation S) :
    runtimeDenotation E P o [.bottom] (compile C .done) σ =
      Denotational.fragmentSemantics E P C σ o := by
  rw [runtimeDenotation_compile E P o _ (List.cons_ne_nil _ _)]
  change expect (auxiliarySemantics E (recursiveEnvironment E P) C (dirac σ))
    (runtimeDenotation E P o [.bottom] .done) = _
  have h : runtimeDenotation E P o [.bottom] .done = fun τ => dirac τ o := by
    funext τ
    cases τ <;> rfl
  rw [h, expect_point]
  rfl

theorem denotational_eq_runtime (C : Stmt S) (σ o : Valuation S) :
    Denotational.fragmentSemantics E P C σ o =
      runtimeValue E P o (initialFragment C σ) := by
  apply le_antisymm
  · have h := semantics_le_runtime E P o C .done [.bottom] .bottom
      (List.cons_ne_nil _ _) σ
    have hr : continuation E P o .done [.bottom] = fun τ => dirac τ o :=
      funext (runtime_done_bottom E P o)
    rw [hr] at h
    change expect (auxiliarySemantics E (recursiveEnvironment E P) C (dirac σ))
      (fun τ => dirac τ o) ≤ _ at h
    rw [expect_point] at h
    exact h
  · exact (runtimeValue_le_denotation E P o (initialFragment C σ)).trans_eq
      (runtimeDenotation_initial E P C σ o)

/-- Theorem `thm:equivalence`: equality of the complete output distributions. -/
theorem denotational_eq_operational (C : Stmt S) (σ : Valuation S) :
    Denotational.fragmentSemantics E P C σ = InferenceProof.fragmentSemantics E P C σ := by
  funext o
  rw [denotational_eq_runtime E P C σ o,
    runtimeValue_eq_terminationProbability E P C o _ (initial_inProgram P C σ)]
  rfl

/-- The finite pPDA polynomial system computes the same distribution as the denotation. -/
theorem denotational_eq_polynomial (C : Stmt S) (σ : Valuation S) :
    Denotational.fragmentSemantics E P C σ = polynomialTermination E P C σ := by
  rw [denotational_eq_operational]
  funext o
  exact (polynomialTermination_eq_operational E P C σ o).symm

theorem programSemantics_eq_operational :
    Denotational.programSemantics E P = InferenceProof.programSemantics E P :=
  denotational_eq_operational E P (.call P.dummy P.main) (.normal Store.zero)

theorem queryProgramSemantics_eq_operational :
    Denotational.queryProgramSemantics E P =
      fun σ => InferenceProof.terminationProbability E P (initialQuery P) σ :=
  denotational_eq_operational E P (.sampleQuery P.dummy P.main) (.normal Store.zero)

theorem operational_isSubdistribution (C : Stmt S) (σ : Valuation S) :
    IsSubdistribution (InferenceProof.fragmentSemantics E P C σ) := by
  rw [← denotational_eq_operational E P C σ]
  exact fragmentSemantics_isSubdistribution E P C σ

end

end InferenceProof.Equivalence
