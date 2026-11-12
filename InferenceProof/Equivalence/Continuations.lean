module

public import InferenceProof.Equivalence.SourceEquations
public import InferenceProof.Equivalence.Runtime

set_option linter.style.header false

/-! # Denotation of runtime continuations and saved frames

Returns restore the saved caller store. A rejected query restores its saved
store and retries the same query. These are the continuations in the call and
query diagrams of Section 6, with error propagation made explicit.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (env : Environment S)

def codeWP : Code S → (Store S → ℝ≥0∞) → (Var S → Store S → ℝ≥0∞) →
    (Store S → ℝ≥0∞) → ℝ≥0∞ → Store S → ℝ≥0∞
  | .done, K, _, _, _ => K
  | .stmt C, K, _, _, e => fun σ => sourceWP E env C (reward K e) (.normal σ)
  | .seq a b, K, R, Q, e => codeWP a (codeWP b K R Q e) R Q e
  | .ret out, _, R, _, _ => R out
  | .endQuery, _, _, Q, _ => Q

theorem codeWP_append (a b : Code S) (K : Store S → ℝ≥0∞)
    (R : Var S → Store S → ℝ≥0∞) (Q : Store S → ℝ≥0∞) (e : ℝ≥0∞) :
    codeWP E env (a.append b) K R Q e = codeWP E env a (codeWP E env b K R Q e) R Q e := by
  induction a generalizing K with
  | seq a c iha ihc => exact congrArg (fun k => codeWP E env a k R Q e) (ihc K)
  | _ => rfl

theorem codeWP_compile (C : Stmt S) (k : Code S) (K : Store S → ℝ≥0∞)
    (R : Var S → Store S → ℝ≥0∞) (Q : Store S → ℝ≥0∞) (e : ℝ≥0∞) (σ : Store S) :
    codeWP E env (compile C k) K R Q e σ =
      sourceWP E env C (reward (codeWP E env k K R Q e) e) (.normal σ) := by
  induction C generalizing k σ with
  | seq a b iha ihb =>
    rw [compile_seq, iha, sourceWP_seq]
    congr 1
    funext τ
    cases τ with
    | normal τ => exact ihb k τ
    | error => rw [sourceWP_error]; rfl
  | _ => rfl

variable (P : Program S) (o : Valuation S)

def runtimeDenotation : List (StackSymbol S) → Code S → Valuation S → ℝ≥0∞
  | [], _, σ => dirac σ o
  | .bottom :: _, k, σ => match σ with
      | .error => dirac .error o
      | .normal σ => codeWP E (recursiveEnvironment E P) k
          (fun τ => dirac (.normal τ) o) (fun _ _ => 0) (fun _ => 0) (dirac .error o) σ
  | .function k x saved :: G, c, σ => match σ with
      | .error => runtimeDenotation G .done .error
      | .normal σ => codeWP E (recursiveEnvironment E P) c (fun _ => 0)
          (fun out τ => runtimeDenotation G k (.normal (saved.update x (τ out))))
          (fun _ => 0) (runtimeDenotation G .done .error) σ
  | .query x f k saved :: G, c, σ => match σ with
      | .error => runtimeDenotation G (compile (.sampleQuery x f) k) (.normal saved)
      | .normal σ => codeWP E (recursiveEnvironment E P) c (fun _ => 0) (fun _ _ => 0)
          (fun τ => runtimeDenotation G k (.normal τ))
          (runtimeDenotation G (compile (.sampleQuery x f) k) (.normal saved)) σ

theorem runtimeDenotation_error (G : List (StackSymbol S)) (a b : Code S) :
    runtimeDenotation E P o G a .error = runtimeDenotation E P o G b .error := by
  cases G with
  | nil => rfl
  | cons X G => cases X <;> rfl

theorem runtimeDenotation_compile (G : List (StackSymbol S)) (hn : G ≠ [])
    (C : Stmt S) (k : Code S) (σ : Valuation S) :
    runtimeDenotation E P o G (compile C k) σ =
      sourceWP E (recursiveEnvironment E P) C (runtimeDenotation E P o G k) σ := by
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X G =>
    cases σ with
    | error => rw [sourceWP_error]; exact runtimeDenotation_error E P o _ _ _
    | normal σ =>
      cases X <;> dsimp only [runtimeDenotation]
      all_goals
        rw [codeWP_compile]
        congr 1
        funext τ
        cases τ <;> rfl

theorem runtimeDenotation_atom (G : List (StackSymbol S)) (hn : G ≠ [])
    (C : Stmt S) (k : Code S) (σ : Store S) :
    runtimeDenotation E P o G (.seq (.stmt C) k) (.normal σ) =
      sourceWP E (recursiveEnvironment E P) C (runtimeDenotation E P o G k) (.normal σ) := by
  cases G with
  | nil => exact False.elim (hn rfl)
  | cons X G =>
    cases X <;> dsimp only [runtimeDenotation, codeWP]
    all_goals
      congr 1
      funext τ
      cases τ <;> rfl

theorem runtimeDenotation_return (G : List (StackSymbol S)) (k : Code S)
    (x out : Var S) (saved : Store S) (σ : Valuation S) :
    runtimeDenotation E P o (.function k x saved :: G) (.ret out) σ =
      outputReward x saved (runtimeDenotation E P o G k) (read out σ) := by
  cases σ with
  | normal σ => rfl
  | error => exact runtimeDenotation_error E P o G .done k

theorem runtimeDenotation_call (G : List (StackSymbol S))
    (k : Code S) (x : Var S) (f : FunctionName S) (σ : Store S) :
    runtimeDenotation E P o (.function k x σ :: G)
      (compile (P.functions f).body (.ret (P.functions f).out)) (.normal σ) =
      sourceWP E (recursiveEnvironment E P) (.call x f)
        (runtimeDenotation E P o G k) (.normal σ) := by
  rw [runtimeDenotation_compile E P o _ (List.cons_ne_nil _ _), sourceWP_call_fixedPoint]
  congr 1
  funext τ
  exact runtimeDenotation_return E P o G k x (P.functions f).out σ τ

theorem runtimeDenotation_query (G : List (StackSymbol S)) (hn : G ≠ [])
    (k : Code S) (x : Var S) (f : FunctionName S) (σ : Store S) :
    runtimeDenotation E P o (.query x f k σ :: G)
      (compile (.call x f) .endQuery) (.normal σ) =
      sourceWP E (recursiveEnvironment E P) (.sampleQuery x f)
        (runtimeDenotation E P o G k) (.normal σ) := by
  rw [runtimeDenotation_compile E P o _ (List.cons_ne_nil _ _), sourceWP_call, expect_option]
  change (∑' v, (recursiveEnvironment E P).1 f (.normal σ) (some v) *
      runtimeDenotation E P o G k (.normal (σ.update x v))) +
    (recursiveEnvironment E P).1 f (.normal σ) none *
      runtimeDenotation E P o G (compile (.sampleQuery x f) k) (.normal σ) = _
  rw [runtimeDenotation_compile E P o G hn]
  exact (sourceWP_sampleQuery_fixedPoint E P x f (runtimeDenotation E P o G k) σ).symm

end

end InferenceProof.Equivalence
