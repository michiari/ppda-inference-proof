module

public import InferenceProof.Equivalence.Main

set_option linter.style.header false

/-! # The appendix's bounded-loop source statements

The source unrollings are Phi iterates from `errorPart`, the denotation of
`diverge`. As in the appendix, they lie between successive zero-seed iterates
and have the same supremum.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Equivalence

open PPDA Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

/-- The value supplied as `true` must be nonzero in the theorems below. -/
def diverge (trueValue : Value S) : Stmt S := .while (.const trueValue) .skip

def boundedWhile (trueValue : Value S) (b : Expr S) (body : Stmt S) : ℕ → Stmt S
  | 0 => diverge trueValue
  | n + 1 => .ite b (.seq body (boundedWhile trueValue b body n)) .skip

theorem semantics_diverge (v : Value S) (hv : v.val ≠ 0) :
    semantics E P (diverge v) = errorPart := by
  classical
  have hfinite : ∀ n (σ : Store S),
      whileApproximation E (.const v) id n (dirac (.normal σ)) = 0 := by
    intro n
    induction n with
    | zero => intro σ; rfl
    | succ n ih =>
      intro σ
      rw [whileApproximation, Function.iterate_succ_apply']
      change whileFunctional E (.const v) id (whileApproximation E (.const v) id n)
        (dirac (.normal σ)) = 0
      unfold whileFunctional
      rw [restrict_dirac_normal, restrict_dirac_normal, errorPart_dirac_normal]
      have hd : decide (((Expr.const v).eval E σ).val ≠ 0) = true := decide_eq_true hv
      rw [hd]
      simpa only [Bool.true_eq_false, ite_false, ite_true, id_eq, zero_add, add_zero]
        using ih σ
  have hpoint : ∀ τ : Valuation S, semantics E P (diverge v) (dirac τ) =
      errorPart (dirac τ) := by
    intro τ
    cases τ with
    | error => rw [semantics_error, errorPart_dirac_error]
    | normal σ =>
      rw [errorPart_dirac_normal]
      change (⨆ n, whileApproximation E (.const v) id n) (dirac (.normal σ)) = 0
      simp only [iSup_apply, hfinite, iSup_const]
  funext p
  rw [semantics_massLinear E P (diverge v), errorPart_massLinear]
  congr 1
  exact funext hpoint

theorem semantics_boundedWhile_succ (v : Value S) (b : Expr S) (body : Stmt S) (n : ℕ) :
    semantics E P (boundedWhile v b body (n + 1)) =
      whileFunctional E b (semantics E P body) (semantics E P (boundedWhile v b body n)) := by
  funext p
  change _ + _ + errorPart p = _ + _ + errorPart p
  exact congrArg (fun q => q + errorPart p) (add_comm _ _)

theorem semantics_boundedWhile_iterate (v : Value S) (hv : v.val ≠ 0)
    (b : Expr S) (body : Stmt S) (n : ℕ) :
    semantics E P (boundedWhile v b body n) =
      (whileFunctional E b (semantics E P body))^[n] errorPart := by
  induction n with
  | zero => exact semantics_diverge E P v hv
  | succ n ih => rw [semantics_boundedWhile_succ, ih, Function.iterate_succ_apply']

theorem semantics_while_eq_iSup_boundedWhile (v : Value S) (hv : v.val ≠ 0)
    (b : Expr S) (body : Stmt S) :
    semantics E P (.while b body) = ⨆ n, semantics E P (boundedWhile v b body n) := by
  simp_rw [semantics_boundedWhile_iterate E P v hv]
  let F := whileFunctional E b (semantics E P body)
  have hm : Monotone F := whileFunctional_monotone E b _
  have he : errorPart (S := S) ≤ F ⊥ := by
    intro p τ
    change errorPart p τ ≤ restrict E b false p τ + 0 + errorPart p τ
    simpa only [zero_add, add_zero] using
      add_le_add (show (0 : ℝ≥0∞) ≤ restrict E b false p τ from zero_le)
        (le_refl (errorPart p τ))
  change (⨆ n, F^[n] ⊥) = ⨆ n, F^[n] errorPart
  apply le_antisymm
  · apply iSup_le
    intro n
    exact le_iSup_of_le n ((hm.iterate n) bot_le)
  · apply iSup_le
    intro n
    apply le_iSup_of_le (n + 1)
    rw [Function.iterate_succ_apply]
    exact (hm.iterate n) he

theorem operational_while_eq_iSup_boundedWhile (v : Value S) (hv : v.val ≠ 0)
    (b : Expr S) (body : Stmt S) (σ : Valuation S) :
    InferenceProof.fragmentSemantics E P (.while b body) σ =
      ⨆ n, InferenceProof.fragmentSemantics E P (boundedWhile v b body n) σ := by
  simp_rw [← denotational_eq_operational E P]
  change semantics E P (.while b body) (dirac σ) = _
  rw [semantics_while_eq_iSup_boundedWhile E P v hv]
  simp only [iSup_apply, Denotational.fragmentSemantics]

theorem boundedWhile_equivalence (v : Value S) (b : Expr S) (body : Stmt S)
    (n : ℕ) (σ : Valuation S) :
    Denotational.fragmentSemantics E P (boundedWhile v b body n) σ =
      InferenceProof.fragmentSemantics E P (boundedWhile v b body n) σ :=
  denotational_eq_operational E P _ σ

end

end InferenceProof.Equivalence
