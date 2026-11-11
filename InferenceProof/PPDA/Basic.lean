module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option linter.style.header false

/-!
# Probabilistic pushdown automata

The finite-control model of Section 2 of `paper/2-background.tex`.
The first symbol of a stack word is its top. Empty-stack configurations are
terminal: we omit their absorbing self-loop when counting first-hit paths.
-/

@[expose] public section

namespace InferenceProof.PPDA

/-- A replacement word of length at most two. -/
inductive Replacement (Γ : Type*) where
  | pop
  | one (symbol : Γ)
  | two (first second : Γ)
  deriving DecidableEq, Fintype

/-- The word that replaces the current top symbol. -/
def Replacement.word {Γ : Type*} : Replacement Γ → List Γ
  | .pop => []
  | .one X => [X]
  | .two X Y => [X, Y]

/-- A rational pPDA transition table on finite control and stack alphabets. -/
structure Automaton (Q Γ : Type*) [Fintype Q] [Fintype Γ] where
  transition : Q → Γ → Q → Replacement Γ → ℚ
  nonnegative : ∀ p X q w, 0 ≤ transition p X q w
  normalized : ∀ p X, ∑ q, ∑ w, transition p X q w = 1

open scoped ENNReal

/-- Embed the exact rational transition coefficient into nonnegative extended reals. -/
noncomputable def Automaton.weight {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    (A : Automaton Q Γ) (p : Q) (X : Γ) (q : Q) (w : Replacement Γ) : ℝ≥0∞ :=
  ENNReal.ofReal (A.transition p X q w : ℝ)

/-- A configuration has a control state and the full (possibly empty) stack. -/
abbrev Configuration (Q Γ : Type*) := Q × List Γ

end InferenceProof.PPDA
