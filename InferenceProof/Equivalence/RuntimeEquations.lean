module

public import InferenceProof.Equivalence.Runtime
public import InferenceProof.Equivalence.SourceEquations

set_option linter.style.header false

/-! # The operational continuation equations of the Section 6 diagrams -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (o : Valuation S)

abbrev continuation (k : Code S) (G : List (StackSymbol S)) (σ : Valuation S) : ℝ≥0∞ :=
  runtimeValue E P o ⟨k, σ, G⟩

theorem runtime_cons (k : Code S) (σ : Valuation S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (hb : Boundary X tail) :
    continuation E P o k (X :: tail) σ =
      ∑ b : Bool, (headMove E P (k, σ) X b).elim 0
        (fun m => ENNReal.ofReal (m.probability : ℝ) *
          runtimeValue E P o (moveTarget m tail)) := by
  classical
  calc
    _ = headFunctional E P o (runtimeValue E P o) ⟨k, σ, X :: tail⟩ :=
      (congrFun (runtimeValue_fixedPoint E P o) _).symm
    _ = _ := by
      simp only [headFunctional, hb, ite_true]
      exact sum_branches E P (k, σ) X (fun m =>
        ENNReal.ofReal (m.probability : ℝ) * runtimeValue E P o (moveTarget m tail))

theorem runtime_empty (σ : Valuation S) :
    continuation E P o .done [] σ = dirac σ o := by
  classical
  have h := congrFun (runtimeValue_fixedPoint E P o) ⟨.done, σ, []⟩
  change dirac (⟨.done, o, []⟩ : Configuration S) ⟨.done, σ, []⟩ =
    continuation E P o .done [] σ at h
  exact h.symm.trans (by simp [dirac, eq_comm])

theorem runtime_error_bottom (k : Code S) :
    continuation E P o k [.bottom] .error = dirac .error o := by
  rw [runtime_cons E P o k .error .bottom [] rfl]
  simp only [headMove, single, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
    Option.elim_none, Option.elim_some, zero_add, Rat.cast_one,
    ENNReal.ofReal_one, one_mul, moveTarget, Replacement.word, List.nil_append]
  exact runtime_empty E P o .error

theorem runtime_done_bottom (σ : Valuation S) :
    continuation E P o .done [.bottom] σ = dirac σ o := by
  cases σ with
  | error => exact runtime_error_bottom E P o .done
  | normal σ =>
    rw [runtime_cons E P o .done (.normal σ) .bottom [] rfl]
    simpa [headMove, single, moveTarget, Replacement.word] using runtime_empty E P o (.normal σ)

theorem runtime_error_function (k c : Code S) (x : Var S) (σ : Store S)
    (G : List (StackSymbol S)) (hn : G ≠ []) :
    continuation E P o c (.function k x σ :: G) .error = continuation E P o c G .error := by
  rw [runtime_cons E P o c .error (.function k x σ) G hn]
  simp [headMove, single, moveTarget, Replacement.word]

theorem runtime_error_query (k c : Code S) (x : Var S) (f : FunctionName S) (σ : Store S)
    (G : List (StackSymbol S)) (hn : G ≠ []) :
    continuation E P o c (.query x f k σ :: G) .error =
      continuation E P o (compile (.sampleQuery x f) k) G (.normal σ) := by
  rw [runtime_cons E P o c .error (.query x f k σ) G hn]
  simp [headMove, single, moveTarget, Replacement.word, compile, Code.ofStmt,
    Code.append]

theorem runtime_error_independent (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ [])
    (a b : Code S) : continuation E P o a G .error = continuation E P o b G .error := by
  induction hg with
  | empty => exact False.elim (hn rfl)
  | bottom => rw [runtime_error_bottom, runtime_error_bottom]
  | function hg ne ih =>
    rw [runtime_error_function E P o _ _ _ _ _ ne,
      runtime_error_function E P o _ _ _ _ _ ne]
    exact ih ne
  | query hg ne ih =>
    rw [runtime_error_query E P o _ _ _ _ _ _ ne,
      runtime_error_query E P o _ _ _ _ _ _ ne]

theorem runtime_return (k : Code S) (x out : Var S) (saved σ : Store S)
    (G : List (StackSymbol S)) (hn : G ≠ []) :
    continuation E P o (.ret out) (.function k x saved :: G) (.normal σ) =
      continuation E P o k G (.normal (saved.update x (σ out))) := by
  rw [runtime_cons E P o (.ret out) (.normal σ) (.function k x saved) G hn]
  simp [headMove, single, moveTarget, Replacement.word]

theorem runtime_endQuery (k : Code S) (x : Var S) (f : FunctionName S) (saved σ : Store S)
    (G : List (StackSymbol S)) (hn : G ≠ []) :
    continuation E P o .endQuery (.query x f k saved :: G) (.normal σ) =
      continuation E P o k G (.normal σ) := by
  rw [runtime_cons E P o .endQuery (.normal σ) (.query x f k saved) G hn]
  simp [headMove, single, moveTarget, Replacement.word]

theorem runtime_skip (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile .skip k) G (.normal σ) =
      continuation E P o k G (.normal σ) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    simp [headMove, single, moveTarget, Replacement.word,
      compile, Code.ofStmt, Code.append]

theorem runtime_assign (x : Var S) (a : Expr S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.assign x a) k) G (.normal σ) =
      continuation E P o k G (.normal (σ.update x (a.eval E σ))) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    simp [headMove, single, moveTarget, Replacement.word,
      compile, Code.ofStmt, Code.append]

theorem runtime_observe (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile .observe k) G (.normal σ) =
      continuation E P o k G .error := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    simp [headMove, single, moveTarget, Replacement.word,
      compile, Code.ofStmt, Code.append]

theorem runtime_ite (b : Expr S) (t f : Stmt S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.ite b t f) k) G (.normal σ) =
      if (b.eval E σ).val = 0 then
        continuation E P o (compile f k) G (.normal σ)
      else continuation E P o (compile t k) G (.normal σ) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    by_cases h : (b.eval E σ).val = 0 <;>
      simp [headMove, single, moveTarget, Replacement.word,
        compile, Code.ofStmt, Code.append, h]

theorem runtime_while (b : Expr S) (body : Stmt S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.while b body) k) G (.normal σ) =
      if (b.eval E σ).val = 0 then continuation E P o k G (.normal σ)
      else continuation E P o (compile body (compile (.while b body) k)) G (.normal σ) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    by_cases h : (b.eval E σ).val = 0 <;>
      simp [headMove, single, moveTarget, Replacement.word,
        compile, Code.ofStmt, Code.append, h]

theorem runtime_call (x : Var S) (f : FunctionName S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.call x f) k) G (.normal σ) =
      continuation E P o (compile (P.functions f).body (.ret (P.functions f).out))
        (.function k x σ :: G) ((P.functions f).init (.normal σ)) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    simp [headMove, single, moveTarget, Replacement.word,
      compile, Code.ofStmt, Code.append]

theorem runtime_sampleQuery (x : Var S) (f : FunctionName S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.sampleQuery x f) k) G (.normal σ) =
      continuation E P o (compile (.call x f) .endQuery) (.query x f k σ :: G) (.normal σ) := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    simp [headMove, single, moveTarget, Replacement.word,
      compile, Code.ofStmt, Code.append]

open scoped Classical in
theorem runtime_randomAssign (x : Var S) (a n d b : Expr S) (k : Code S) (σ : Store S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ []) :
    continuation E P o (compile (.randomAssign x a n d b) k) G (.normal σ) =
      if ValidProbability E σ n d then
        ENNReal.ofReal (branchProbability E σ n d : ℝ) * continuation E P o k G
            (.normal (σ.update x (a.eval E σ))) +
          ENNReal.ofReal ((1 - branchProbability E σ n d : ℚ) : ℝ) *
            continuation E P o k G (.normal (σ.update x (b.eval E σ)))
      else 0 := by
  classical
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X tail =>
    rw [runtime_cons E P o _ _ X tail hg.boundary]
    by_cases hv : ValidProbability E σ n d
    · by_cases he : a.eval E σ = b.eval E σ
      · have hw := branchProbability_weights_sum E σ n d hv
        simp only [Rat.cast_sub, Rat.cast_one] at hw
        simp [headMove, single, moveTarget, Replacement.word, compile, Code.ofStmt,
          Code.append, hv, he, ← add_mul, hw]
      · simp [headMove, moveTarget, Replacement.word, compile, Code.ofStmt,
          Code.append, hv, he, add_comm]
    · simp [headMove, moveTarget, Replacement.word, compile, Code.ofStmt, Code.append, hv]

end

end InferenceProof.Equivalence
