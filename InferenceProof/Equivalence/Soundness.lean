module

public import InferenceProof.Equivalence.Continuations

set_option linter.style.header false

/-! # Every operational terminating run is accounted for by the denotation

The source fixed-point equations make the denotation of code and saved frames
a pre-fixed point of the runtime first-step operator. Leastness bounds the sum
of all finite runs. This packages the diagram arguments without identifying
different random branches or assuming a run-decomposition theorem.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (o : Valuation S)

theorem sum_single (m : Move S) (F : Move S → ℝ≥0∞) :
    (∑ b : Bool, (single b m).elim 0 F) = F m := by simp [single]

theorem denotation_atom_step (X : StackSymbol S) (G : List (StackSymbol S))
    (s : Stmt S) (k : Code S) (σ : Store S) :
    (∑ b : Bool, (headMove E P (.seq (.stmt s) k, .normal σ) X b).elim 0
      (fun m => ENNReal.ofReal (m.probability : ℝ) *
        runtimeDenotation E P o (moveTarget m G).stack
          (moveTarget m G).code (moveTarget m G).store)) ≤
      sourceWP E (recursiveEnvironment E P) s (runtimeDenotation E P o (X :: G) k)
        (.normal σ) := by
  classical
  have hn : X :: G ≠ [] := List.cons_ne_nil _ _
  cases s with
  | skip =>
    simp only [headMove, sum_single, moveTarget, Replacement.word, List.cons_append,
      List.nil_append, Rat.cast_one, ENNReal.ofReal_one, one_mul, sourceWP_skip, le_refl]
  | assign x a =>
    simp only [headMove, sum_single, moveTarget, Replacement.word, List.cons_append,
      List.nil_append, Rat.cast_one, ENNReal.ofReal_one, one_mul, sourceWP_assign, le_refl]
  | observe =>
    simp only [headMove, sum_single, moveTarget, Replacement.word, List.cons_append,
      List.nil_append, Rat.cast_one, ENNReal.ofReal_one, one_mul, sourceWP_observe, le_refl]
  | randomAssign x a n d b =>
    by_cases hv : ValidProbability E σ n d
    · by_cases he : a.eval E σ = b.eval E σ
      · rw [sourceWP_randomAssign_eq E _ x a n d b _ σ hv he]
        simp [headMove, single, hv, he, moveTarget, Replacement.word]
      · rw [sourceWP_randomAssign]
        simp [headMove, hv, he, moveTarget, Replacement.word, add_comm]
    · rw [sourceWP_randomAssign]
      simp [headMove, hv]
  | ite b t f =>
    rw [sourceWP_ite]
    by_cases h : (b.eval E σ).val = 0 <;>
      simp only [headMove, h, ite_true, ite_false, sum_single, moveTarget,
        Replacement.word, List.cons_append, List.nil_append, Rat.cast_one,
        ENNReal.ofReal_one, one_mul, runtimeDenotation_compile E P o _ hn, le_refl]
  | «while» b body =>
    rw [sourceWP_while]
    by_cases h : (b.eval E σ).val = 0
    · simp only [headMove, h, ite_true, sum_single, moveTarget,
        Replacement.word, List.cons_append, List.nil_append, Rat.cast_one,
        ENNReal.ofReal_one, one_mul, le_refl]
    · simp only [headMove, h, ite_false, sum_single, moveTarget,
        Replacement.word, List.cons_append, List.nil_append, Rat.cast_one,
        ENNReal.ofReal_one, one_mul]
      change runtimeDenotation E P o (X :: G)
        (compile body (compile (.while b body) k)) (.normal σ) ≤ _
      rw [runtimeDenotation_compile E P o _ hn]
      have heq := funext (runtimeDenotation_compile E P o (X :: G) hn (.while b body) k)
      rw [heq]
  | call x f =>
    simp only [headMove, sum_single, moveTarget, Replacement.word, List.cons_append,
      List.nil_append, Rat.cast_one, ENNReal.ofReal_one, one_mul]
    exact (runtimeDenotation_call E P o (X :: G) k x f σ).le
  | sampleQuery x f =>
    simp only [headMove, sum_single, moveTarget, Replacement.word, List.cons_append,
      List.nil_append, Rat.cast_one, ENNReal.ofReal_one, one_mul]
    exact (runtimeDenotation_query E P o (X :: G) hn k x f σ).le
  | seq a b => simp only [headMove, Option.elim_none, Finset.sum_const_zero]; exact zero_le

def configurationDenotation (c : Configuration S) : ℝ≥0∞ :=
  runtimeDenotation E P o c.stack c.code c.store

theorem configurationDenotation_prefixed :
    headFunctional E P o (configurationDenotation E P o) ≤ configurationDenotation E P o := by
  classical
  rintro ⟨code, state, stack⟩
  cases stack with
  | nil =>
    change dirac (⟨.done, o, []⟩ : Configuration S) ⟨code, state, []⟩ ≤ dirac state o
    by_cases h : (⟨.done, o, []⟩ : Configuration S) = ⟨code, state, []⟩
    · have hs : o = state := congrArg Configuration.store h
      have hk : Code.done = code := congrArg Configuration.code h
      simp [dirac, hs, hk]
    · simp [dirac, h]
  | cons X G =>
    simp only [headFunctional]
    split_ifs with hb
    · rw [sum_branches E P (code, state) X (fun m =>
        ENNReal.ofReal (m.probability : ℝ) * configurationDenotation E P o (moveTarget m G))]
      change (∑ b : Bool, (headMove E P (code, state) X b).elim 0
        (fun m => ENNReal.ofReal (m.probability : ℝ) *
          runtimeDenotation E P o (moveTarget m G).stack
            (moveTarget m G).code (moveTarget m G).store)) ≤ _
      cases state with
      | error =>
        cases X with
        | bottom =>
          change G = [] at hb
          subst G
          simp [headMove, single, moveTarget, Replacement.word,
            configurationDenotation, runtimeDenotation]
        | function k x saved =>
          simp only [headMove, sum_single, moveTarget, Replacement.word, List.nil_append,
            Rat.cast_one, ENNReal.ofReal_one, one_mul, configurationDenotation,
            runtimeDenotation]
          exact (runtimeDenotation_error E P o G code .done).le
        | query x f k saved =>
          simp [headMove, single, moveTarget, Replacement.word,
            configurationDenotation, runtimeDenotation, compile, Code.ofStmt, Code.append]
      | normal σ =>
        cases code with
        | done =>
          cases X with
          | bottom =>
            change G = [] at hb
            subst G
            simp [headMove, single, moveTarget, Replacement.word,
              configurationDenotation, runtimeDenotation, codeWP]
          | function | query => simp [headMove]
        | ret out =>
          cases X with
          | function k x saved =>
            simp [headMove, single, moveTarget, Replacement.word,
              configurationDenotation, runtimeDenotation, codeWP]
          | bottom | query => simp [headMove]
        | endQuery =>
          cases X with
          | query x f k saved =>
            simp [headMove, single, moveTarget, Replacement.word,
              configurationDenotation, runtimeDenotation, codeWP]
          | bottom | function => simp [headMove]
        | stmt s => simp [headMove]
        | seq first k =>
          cases first with
          | stmt s =>
            change _ ≤ runtimeDenotation E P o (X :: G) (.seq (.stmt s) k) (.normal σ)
            rw [runtimeDenotation_atom E P o _ (List.cons_ne_nil _ _)]
            exact denotation_atom_step E P o X G s k σ
          | done | seq | ret | endQuery => simp [headMove]
    · exact zero_le

theorem runtimeValue_le_denotation (c : Configuration S) :
    runtimeValue E P o c ≤ runtimeDenotation E P o c.stack c.code c.store :=
  runtimeValue_le E P o (configurationDenotation_prefixed E P o) c

end

end InferenceProof.Equivalence
