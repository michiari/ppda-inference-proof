module

public import InferenceProof.Equivalence.LoopApproximants

set_option linter.style.header false

/-! # Structural induction, including finite loop unfoldings

An environment is bounded by the runtime if its call and query kernels can
be executed before every continuation. This is the induction invariant for
the k-bounded calls of Section 6; it is proved for all finite iterates below.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (o : Valuation S)

def CallsBelow (env : Environment S) : Prop :=
  (∀ (x : Var S) (f : FunctionName S) (k : Code S) (G : List (StackSymbol S)),
    Grounded G → G ≠ [] → ∀ σ : Store S,
      sourceWP E env (.call x f) (continuation E P o k G) (.normal σ) ≤
        continuation E P o (compile (.call x f) k) G (.normal σ)) ∧
  (∀ (x : Var S) (f : FunctionName S) (k : Code S) (G : List (StackSymbol S)),
    Grounded G → G ≠ [] → ∀ σ : Store S,
      sourceWP E env (.sampleQuery x f) (continuation E P o k G) (.normal σ) ≤
        continuation E P o (compile (.sampleQuery x f) k) G (.normal σ))

theorem sourceWP_bound_of_normal (env : Environment S) (C : Stmt S) (k : Code S)
    (G : List (StackSymbol S)) (hg : Grounded G) (hn : G ≠ [])
    (h : ∀ σ : Store S, sourceWP E env C (continuation E P o k G) (.normal σ) ≤
      continuation E P o (compile C k) G (.normal σ)) (σ : Valuation S) :
    sourceWP E env C (continuation E P o k G) σ ≤
      continuation E P o (compile C k) G σ := by
  cases σ with
  | normal σ => exact h σ
  | error =>
    rw [sourceWP_error, runtime_error_independent E P o G hg hn k (compile C k)]

theorem auxiliarySemantics_le_runtime (env : Environment S) (henv : CallsBelow E P o env)
    (C : Stmt S) (k : Code S) (G : List (StackSymbol S))
    (hg : Grounded G) (hn : G ≠ []) (σ : Valuation S) :
    sourceWP E env C (continuation E P o k G) σ ≤
      continuation E P o (compile C k) G σ := by
  classical
  suffices hnormal : ∀ (C : Stmt S) (k : Code S) (G : List (StackSymbol S)),
      Grounded G → G ≠ [] → ∀ σ : Store S,
        sourceWP E env C (continuation E P o k G) (.normal σ) ≤
          continuation E P o (compile C k) G (.normal σ) from
    sourceWP_bound_of_normal E P o env C k G hg hn (hnormal C k G hg hn) σ
  intro C
  induction C with
  | skip =>
    intro k G hg hn σ
    rw [sourceWP_skip, runtime_skip E P o k σ G hg hn]
  | assign x a =>
    intro k G hg hn σ
    rw [sourceWP_assign, runtime_assign E P o x a k σ G hg hn]
  | randomAssign x a n d b =>
    intro k G hg hn σ
    rw [sourceWP_randomAssign, runtime_randomAssign E P o x a n d b k σ G hg hn]
  | observe =>
    intro k G hg hn σ
    rw [sourceWP_observe, runtime_observe E P o k σ G hg hn]
  | call x f => exact henv.1 x f
  | sampleQuery x f => exact henv.2 x f
  | ite b t f iht ihf =>
    intro k G hg hn σ
    rw [sourceWP_ite, runtime_ite E P o b t f k σ G hg hn]
    split_ifs
    · exact ihf k G hg hn σ
    · exact iht k G hg hn σ
  | seq a b iha ihb =>
    intro k G hg hn σ
    rw [sourceWP_seq, compile_seq]
    apply le_trans _ (iha (compile b k) G hg hn σ)
    apply sourceWP_mono
    exact sourceWP_bound_of_normal E P o env b k G hg hn (ihb k G hg hn)
  | «while» b body ih =>
    intro k G hg hn σ
    let loop := compile (.while b body) k
    have hfinite : ∀ n (τ : Valuation S),
        expect (whileApproximation E b (auxiliarySemantics E env body) n (dirac τ))
          (continuation E P o k G) ≤ continuation E P o loop G τ := by
      intro n
      induction n with
      | zero =>
        intro τ
        change expect 0 (continuation E P o k G) ≤ _
        rw [expect_zero]
        exact zero_le
      | succ n ihn =>
        intro τ
        cases τ with
        | error =>
          rw [expect_whileApproximation_error E b _
            (auxiliarySemantics_massLinear E env body)]
          exact (runtime_error_independent E P o G hg hn k loop).le
        | normal τ =>
          rw [expect_whileApproximation_succ E b _
            (auxiliarySemantics_massLinear E env body)]
          rw [show loop = compile (.while b body) k from rfl,
            runtime_while E P o b body k τ G hg hn]
          split_ifs
          · rfl
          · exact (expect_mono le_rfl ihn).trans (ih loop G hg hn τ)
    change expect (whileSemantics E b (auxiliarySemantics E env body)
      (dirac (.normal σ))) (continuation E P o k G) ≤ _
    have hsup : whileSemantics E b (auxiliarySemantics E env body) (dirac (.normal σ)) =
        ⨆ n, whileApproximation E b (auxiliarySemantics E env body) n
          (dirac (.normal σ)) := by simp only [whileSemantics, iSup_apply]
    rw [hsup, expect_iSup _ (fun i j hij =>
      whileApproximation_monotone E b _ hij (dirac (.normal σ)))]
    exact iSup_le fun n => hfinite n (.normal σ)

end

end InferenceProof.Equivalence
