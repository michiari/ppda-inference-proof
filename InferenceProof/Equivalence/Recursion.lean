module

public import InferenceProof.Equivalence.Structural

set_option linter.style.header false

/-! # Bounded calls, bounded query retries, and their increasing supremum

The induction on k uses exactly alpha_(k+1) = body(alpha_k,beta_k) and
beta_(k+1) = success(alpha_k) + alpha_k(err) beta_k. Instead of adding
bounded instructions to the source AST, the bound is carried by the semantic
environment. Every finite approximation is realized before every runtime
continuation, and continuity removes the bound.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (o : Valuation S)

theorem recursionApproximation_callsBelow (n : ℕ) :
    CallsBelow E P o (recursionApproximation E P n) := by
  induction n with
  | zero =>
    constructor
    · intro x f k G hg hn σ
      rw [sourceWP_call]
      change expect 0 _ ≤ _
      rw [expect_zero]
      exact zero_le
    · intro x f k G hg hn σ
      rw [sourceWP_sampleQuery]
      simp [recursionApproximation]
  | succ n ih =>
    constructor
    · intro x f k G hg hn σ
      rw [sourceWP_call_succ, runtime_call E P o x f k σ G hg hn]
      apply le_trans _ (auxiliarySemantics_le_runtime E P o _ ih (P.functions f).body
        (.ret (P.functions f).out) (.function k x σ :: G) (.function hg hn)
        (List.cons_ne_nil _ _) (.normal σ))
      apply sourceWP_mono
      intro τ
      cases τ with
      | normal τ =>
        exact (runtime_return E P o k x (P.functions f).out σ τ G hn).symm.le
      | error =>
        rw [runtime_error_function E P o k (.ret (P.functions f).out) x σ G hn]
        exact (runtime_error_independent E P o G hg hn k (.ret (P.functions f).out)).le
    · intro x f k G hg hn σ
      rw [sourceWP_sampleQuery_succ, runtime_sampleQuery E P o x f k σ G hg hn]
      calc
        _ ≤ (∑' v, (recursionApproximation E P n).1 f (.normal σ) (some v) *
              continuation E P o k G (.normal (σ.update x v))) +
            (recursionApproximation E P n).1 f (.normal σ) none *
              continuation E P o (compile (.sampleQuery x f) k) G (.normal σ) :=
          add_le_add le_rfl (mul_le_mul' le_rfl (ih.2 x f k G hg hn σ))
        _ = sourceWP E (recursionApproximation E P n) (.call x f)
            (continuation E P o .endQuery (.query x f k σ :: G)) (.normal σ) := by
          rw [sourceWP_call, expect_option]
          congr 1
          · apply tsum_congr
            intro v
            exact congrArg (fun z => (recursionApproximation E P n).1 f (.normal σ)
              (some v) * z) (runtime_endQuery E P o k x f σ (σ.update x v) G hn).symm
          · exact congrArg (fun z => (recursionApproximation E P n).1 f (.normal σ)
              none * z) (runtime_error_query E P o k .endQuery x f σ G hn).symm
        _ ≤ _ := ih.1 x f .endQuery (.query x f k σ :: G) (.query hg hn)
          (List.cons_ne_nil _ _) σ

theorem sourceWP_recursiveEnvironment (C : Stmt S) (r : Valuation S → ℝ≥0∞)
    (σ : Valuation S) :
    sourceWP E (recursiveEnvironment E P) C r σ =
      ⨆ n, sourceWP E (recursionApproximation E P n) C r σ := by
  change expect (auxiliarySemantics E (⨆ n, recursionApproximation E P n) C (dirac σ)) r = _
  rw [auxiliarySemantics_iSup E C _ (recursionApproximation_monotone E P)]
  simp only [iSup_apply]
  exact expect_iSup _ (fun i j hij =>
    auxiliarySemantics_monotone E C (recursionApproximation_monotone E P hij) (dirac σ)) r

theorem semantics_le_runtime (C : Stmt S) (k : Code S) (G : List (StackSymbol S))
    (hg : Grounded G) (hn : G ≠ []) (σ : Valuation S) :
    sourceWP E (recursiveEnvironment E P) C (continuation E P o k G) σ ≤
      continuation E P o (compile C k) G σ := by
  rw [sourceWP_recursiveEnvironment]
  exact iSup_le fun n => auxiliarySemantics_le_runtime E P o _
    (recursionApproximation_callsBelow E P o n) C k G hg hn σ

end

end InferenceProof.Equivalence
