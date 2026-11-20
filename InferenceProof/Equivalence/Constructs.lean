module

public import InferenceProof.Equivalence.Main

set_option linter.style.header false

/-! # The paper-facing composition and approximation identities

These corollaries expose the laws used in the appendix and the call/query
diagrams as equalities of distributions, in addition to the stronger
continuation versions used to prove the main theorem.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

/-- Extend the original point-input operational kernel by the paper's delta expansion. -/
def operationalTransformer (C : Stmt S) (p : StoreMass S) : StoreMass S :=
  Denotational.bind p (InferenceProof.fragmentSemantics E P C)

theorem semantics_eq_operationalTransformer (C : Stmt S) :
    semantics E P C = operationalTransformer E P C := by
  funext p
  rw [semantics_massLinear E P C]
  unfold operationalTransformer
  congr 1
  funext σ
  exact denotational_eq_operational E P C σ

/-- Appendix, sequencing: concatenate runs and sum over the intermediate valuation. -/
theorem operational_seq (a b : Stmt S) (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P (.seq a b) σ =
      Denotational.bind (InferenceProof.fragmentSemantics E P a σ)
        (InferenceProof.fragmentSemantics E P b) := by
  rw [← denotational_eq_operational E P (.seq a b) σ]
  change semantics E P b (semantics E P a (dirac σ)) = _
  rw [semantics_eq_operationalTransformer E P b]
  exact congrArg (fun p => Denotational.bind p (InferenceProof.fragmentSemantics E P b))
    (denotational_eq_operational E P a σ)

theorem operational_error (C : Stmt S) :
    InferenceProof.fragmentSemantics E P C .error = dirac .error := by
  rw [← denotational_eq_operational]
  exact semantics_error E P C

theorem operational_skip (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P .skip σ = dirac σ := by
  rw [← denotational_eq_operational]
  rfl

theorem operational_observe (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P .observe σ = dirac .error := by
  rw [← denotational_eq_operational]
  change observe (dirac σ) = _
  rw [observe_eq_bind, bind_dirac]

open scoped Classical in
theorem operational_ite (b : Expr S) (t f : Stmt S) (σ : Store S) :
    InferenceProof.fragmentSemantics E P (.ite b t f) (.normal σ) =
      if (b.eval E σ).val = 0 then InferenceProof.fragmentSemantics E P f (.normal σ)
      else InferenceProof.fragmentSemantics E P t (.normal σ) := by
  classical
  rw [← denotational_eq_operational E P (.ite b t f) (.normal σ),
    ← denotational_eq_operational E P f (.normal σ),
    ← denotational_eq_operational E P t (.normal σ)]
  funext o
  have h := sourceWP_ite E (recursiveEnvironment E P) b t f (fun τ => dirac τ o) σ
  simp only [sourceWP, expect_point] at h
  change auxiliarySemantics E (recursiveEnvironment E P) (.ite b t f)
    (dirac (.normal σ)) o = _
  simpa only [ite_apply, Denotational.fragmentSemantics, semantics] using h

/-- Section 6, equation `eq:op-func`, with initialized callee store. -/
theorem operational_call (x : Var S) (f : FunctionName S) (σ : Store S) :
    InferenceProof.fragmentSemantics E P (.call x f) (.normal σ) =
      Denotational.bind (marginal (P.functions f).out
        (InferenceProof.fragmentSemantics E P (P.functions f).body
          ((P.functions f).init (.normal σ))))
        (fun outcome => match outcome with
          | some v => dirac (.normal (σ.update x v))
          | none => dirac .error) := by
  rw [← denotational_eq_operational E P (.call x f) (.normal σ),
    ← denotational_eq_operational E P (P.functions f).body ((P.functions f).init (.normal σ))]
  change functionAssign x ((recursiveEnvironment E P).1 f) (dirac (.normal σ)) = _
  rw [functionAssign, bind_dirac]
  dsimp only
  have ha : (recursiveEnvironment E P).1 f (.normal σ) =
      marginal (P.functions f).out
        (Denotational.fragmentSemantics E P (P.functions f).body
          ((P.functions f).init (.normal σ))) :=
    (congrFun (congrFun (congrArg Prod.fst
      (recursiveEnvironment_fixedPoint E P)) f) (.normal σ)).symm
  rw [ha]
  rfl

theorem functionSemantics_eq_marginal_operational (f : FunctionName S) (σ : Valuation S) :
    functionSemantics E P f σ = marginal (P.functions f).out
      (InferenceProof.fragmentSemantics E P (P.functions f).body ((P.functions f).init σ)) := by
  rw [← denotational_eq_operational E P (P.functions f).body ((P.functions f).init σ)]
  exact (congrFun (congrFun (congrArg Prod.fst
    (recursiveEnvironment_fixedPoint E P)) f) σ).symm

/-- The recursive-call cutoffs of Section 6 increase to the operational kernel. -/
theorem operational_eq_iSup_recursionApproximation (C : Stmt S) (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P C σ =
      ⨆ n, auxiliarySemantics E (recursionApproximation E P n) C (dirac σ) := by
  rw [← denotational_eq_operational E P C σ]
  change auxiliarySemantics E (recursiveEnvironment E P) C (dirac σ) = _
  rw [recursiveEnvironment, auxiliarySemantics_iSup E C _
    (recursionApproximation_monotone E P)]
  simp only [iSup_apply]

/-- The finite loop iterates used in the appendix recover the operational loop kernel. -/
theorem operational_while_eq_iSup (b : Expr S) (body : Stmt S) (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P (.while b body) σ =
      ⨆ n, whileApproximation E b (operationalTransformer E P body) n (dirac σ) := by
  rw [← denotational_eq_operational E P (.while b body) σ]
  change whileSemantics E b (semantics E P body) (dirac σ) = _
  rw [semantics_eq_operationalTransformer]
  simp only [whileSemantics, iSup_apply]

/-- The affine retry equation in the query diagram, before normalization. -/
theorem operational_sampleQuery (x : Var S) (f : FunctionName S) (σ : Store S) :
    InferenceProof.fragmentSemantics E P (.sampleQuery x f) (.normal σ) =
      fun τ => (∑' v, functionSemantics E P f (.normal σ) (some v) *
        dirac (.normal (σ.update x v)) τ) +
        functionSemantics E P f (.normal σ) none *
          InferenceProof.fragmentSemantics E P (.sampleQuery x f) (.normal σ) τ := by
  simp_rw [← denotational_eq_operational E P (.sampleQuery x f) (.normal σ)]
  funext o
  have h := sourceWP_sampleQuery_fixedPoint E P x f (fun τ => dirac τ o) σ
  simp only [sourceWP, expect_point] at h
  exact h

/-- Operational nested conditioning has the same normalization, retaining divergence mass. -/
theorem operational_sampleQuery_eq_normalize (x : Var S) (f : FunctionName S)
    (σ : Store S) :
    InferenceProof.fragmentSemantics E P (.sampleQuery x f) (.normal σ) =
      sampleQueryAssign x (fun τ => normalize (marginal (P.functions f).out
        (InferenceProof.fragmentSemantics E P (P.functions f).body ((P.functions f).init τ))))
        (dirac (.normal σ)) := by
  rw [← denotational_eq_operational E P (.sampleQuery x f) (.normal σ)]
  change sampleQueryAssign x (sampleQuerySemantics E P f) (dirac (.normal σ)) = _
  have h : sampleQuerySemantics E P f = fun τ => normalize (marginal (P.functions f).out
      (InferenceProof.fragmentSemantics E P (P.functions f).body ((P.functions f).init τ))) := by
    funext τ
    rw [sampleQuerySemantics_eq_normalize, functionSemantics_eq_marginal_operational]
  rw [h]

end

end InferenceProof.Equivalence
