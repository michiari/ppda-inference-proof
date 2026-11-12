module

public import InferenceProof.PPDA.Reachability
public import InferenceProof.Denotational.Order

set_option linter.style.header false

/-! # First-step equations for the existing operational run sum

Finite terminating runs are partitioned into the empty run and a first rule
instance followed by a shorter run. Increasing the length cutoff recovers the
entire run sum. This makes precise the finite-run arguments in Section 6.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

def _root_.InferenceProof.PPDA.OperationalWalk.length {a b : Configuration S} :
    PPDA.OperationalWalk E P a b → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

def walkUnfold (a b : Configuration S) :
    PPDA.OperationalWalk E P a b ≃
      PLift (a = b) ⊕ (Σ edge : FullEdge E P a, PPDA.OperationalWalk E P edge.2.1 b) where
  toFun w := match w with
    | .nil _ => .inl ⟨rfl⟩
    | .cons edge rest => .inr ⟨⟨edge.1, _, edge.2⟩, rest⟩
  invFun w := match w with
    | .inl h => h.down ▸ .nil a
    | .inr ⟨edge, rest⟩ => .cons ⟨edge.1, edge.2.2⟩ rest
  left_inv w := by cases w <;> rfl
  right_inv w := by
    rcases w with ⟨h⟩ | ⟨⟨p, c, step⟩, rest⟩
    · cases h.down; rfl
    · rfl

/-- Bellman's first-step functional, retaining individual rule derivations. -/
def operationalFunctional (σ : Valuation S) (V : Configuration S → ℝ≥0∞)
    (c : Configuration S) : ℝ≥0∞ :=
  dirac ⟨.done, σ, []⟩ c +
    ∑' edge : FullEdge E P c, ENNReal.ofReal (edge.1 : ℝ) * V edge.2.1

def boundedRunSum (σ : Valuation S) (n : ℕ) (c : Configuration S) : ℝ≥0∞ :=
  ∑' w : PPDA.OperationalWalk E P c ⟨.done, σ, []⟩,
    if w.length < n then w.weight else 0

theorem boundedRunSum_zero (σ : Valuation S) : boundedRunSum E P σ 0 = ⊥ := by
  funext c
  simp [boundedRunSum]

theorem boundedRunSum_succ (σ : Valuation S) (n : ℕ) :
    boundedRunSum E P σ (n + 1) = operationalFunctional E P σ (boundedRunSum E P σ n) := by
  classical
  funext c
  unfold boundedRunSum
  rw [← (walkUnfold E P c ⟨.done, σ, []⟩).symm.tsum_eq,
    Summable.tsum_sum ENNReal.summable ENNReal.summable]
  have hnil (h : PLift (c = ⟨.done, σ, []⟩)) :
      (if ((walkUnfold E P c ⟨.done, σ, []⟩).symm (.inl h)).length < n + 1 then
        ((walkUnfold E P c ⟨.done, σ, []⟩).symm (.inl h)).weight else 0) = 1 := by
    rcases h with ⟨h⟩
    cases h
    simp [walkUnfold, PPDA.OperationalWalk.length, PPDA.OperationalWalk.weight]
  simp_rw [hnil]
  change (∑' _h : PLift (c = ⟨.done, σ, []⟩), (1 : ℝ≥0∞)) +
    (∑' z : Σ edge : FullEdge E P c,
      PPDA.OperationalWalk E P edge.2.1 ⟨.done, σ, []⟩,
      if z.2.length + 1 < n + 1 then
        ENNReal.ofReal (z.1.1 : ℝ) * z.2.weight else 0) = _
  rw [ENNReal.tsum_sigma']
  simp only [Nat.add_lt_add_iff_right]
  have hit (a w : ℝ≥0∞) (h : Prop) [Decidable h] :
      (if h then a * w else 0) = a * (if h then w else 0) := by
    split_ifs <;> simp
  simp_rw [hit, ENNReal.tsum_mul_left]
  change _ + _ = dirac ⟨.done, σ, []⟩ c + _
  congr 1
  by_cases h : c = ⟨.done, σ, []⟩
  · subst c
    simp [dirac]
  · have : IsEmpty (PLift (c = ⟨.done, σ, []⟩)) := ⟨fun z => h z.down⟩
    simp [dirac, Ne.symm h]

theorem operationalFunctional_monotone (σ : Valuation S) :
    Monotone (operationalFunctional E P σ) := by
  intro V W h c
  apply add_le_add le_rfl
  exact ENNReal.tsum_le_tsum fun e : FullEdge E P c => mul_le_mul' le_rfl (h e.2.1)

theorem operationalFunctional_omegaContinuous (σ : Valuation S) :
    ChainContinuous (operationalFunctional E P σ) := by
  apply ChainContinuous.of_apply₂
  intro c
  apply omegaContinuous_add ChainContinuous.const
  apply omegaContinuous_tsum
  intro e
  exact omegaContinuous_mul ChainContinuous.const (ChainContinuous.apply e.2.1)

theorem boundedRunSum_eq_iterate (σ : Valuation S) (n : ℕ) :
    boundedRunSum E P σ n = (operationalFunctional E P σ)^[n] ⊥ := by
  induction n with
  | zero => exact boundedRunSum_zero E P σ
  | succ n ih => rw [boundedRunSum_succ, ih, Function.iterate_succ_apply']

theorem terminationProbability_eq_iSup (σ : Valuation S) :
    (fun c => InferenceProof.terminationProbability E P c σ) =
      ⨆ n, boundedRunSum E P σ n := by
  classical
  funext c
  rw [operational_termination_eq_sum_walk]
  simp only [iSup_apply]
  change (∑' w : PPDA.OperationalWalk E P c ⟨.done, σ, []⟩, w.weight) =
    ⨆ n, ∑' w : PPDA.OperationalWalk E P c ⟨.done, σ, []⟩,
      if w.length < n then w.weight else 0
  rw [← tsum_iSup_of_monotone]
  · apply tsum_congr
    intro w
    apply le_antisymm
    · exact le_iSup_of_le (w.length + 1) (by simp)
    · exact iSup_le fun n => by split_ifs <;> simp
  · intro i j hij w
    dsimp only
    split_ifs with hi hj
    · rfl
    · exact False.elim (hj (lt_of_lt_of_le hi hij))
    · exact zero_le
    · rfl

theorem terminationProbability_fixedPoint (σ : Valuation S) :
    operationalFunctional E P σ (fun c => InferenceProof.terminationProbability E P c σ) =
      (fun c => InferenceProof.terminationProbability E P c σ) := by
  rw [terminationProbability_eq_iSup]
  simp_rw [boundedRunSum_eq_iterate]
  exact kleene_fixedPoint _ (operationalFunctional_omegaContinuous E P σ)

theorem terminationProbability_le (σ : Valuation S) {V : Configuration S → ℝ≥0∞}
    (h : operationalFunctional E P σ V ≤ V) :
    (fun c => InferenceProof.terminationProbability E P c σ) ≤ V := by
  rw [terminationProbability_eq_iSup]
  simp_rw [boundedRunSum_eq_iterate]
  exact kleene_le (operationalFunctional_monotone E P σ) h

end

end InferenceProof.Equivalence
