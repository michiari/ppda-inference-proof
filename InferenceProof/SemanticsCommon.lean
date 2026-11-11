module

public import InferenceProof.Syntax
public import Mathlib.Data.Rat.Defs

set_option linter.style.header false

/-!
# Shared definitions for cpGCL semantics

Stores, error valuations, expression interpretation and evaluation, and random
assignment probabilities used by both operational and denotational semantics.
-/

@[expose] public section

namespace InferenceProof

abbrev Store (S : Signature) := Var S → Value S

/-- The paper's ordinary store `σ₀`, initially zero at every variable. -/
def Store.zero {S : Signature} : Store S := fun _ => 0

/-- Store update `σ[x ↦ v]`. -/
def Store.update {S : Signature} (σ : Store S) (x : Var S) (v : Value S) : Store S :=
  Function.update σ x v

/-- `Val = [M]^V ∪ {σ_err}`; error is a separate store, not a variable value. -/
inductive Valuation (S : Signature) where
  | normal (store : Store S)
  | error

/-- Interpret the unspecified fixed-width arithmetic and comparison operators.

This is a parameter, not an axiom: a concrete language supplies these functions,
including its choices for overflow and arithmetic division by zero.
-/
structure ExprInterpretation (S : Signature) where
  unary : S.UnaryOp → Value S → Value S
  binary : S.BinaryOp → Value S → Value S → Value S

/-- Expression evaluation is defined only on ordinary stores. -/
def Expr.eval {S : Signature} (E : ExprInterpretation S) (σ : Store S) :
    Expr S → Value S
  | .const v => v
  | .var x => σ x
  | .unary op e => E.unary op (e.eval E σ)
  | .binary op e₁ e₂ => E.binary op (e₁.eval E σ) (e₂.eval E σ)

/-- The exact rational probability used by a random assignment. -/
def branchProbability {S : Signature} (E : ExprInterpretation S) (σ : Store S)
    (numerator denominator : Expr S) : ℚ :=
  ((numerator.eval E σ).val : ℚ) / ((denominator.eval E σ).val : ℚ)

/-- A random assignment is enabled only for a nonzero denominator and valid probability. -/
def ValidProbability {S : Signature} (E : ExprInterpretation S) (σ : Store S)
    (numerator denominator : Expr S) : Prop :=
  (denominator.eval E σ).val ≠ 0 ∧
    0 ≤ branchProbability E σ numerator denominator ∧
    branchProbability E σ numerator denominator ≤ 1

end InferenceProof
