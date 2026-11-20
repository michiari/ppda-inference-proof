module

public import InferenceProof.PPDA.FiniteModel
public import InferenceProof.PPDA.StepIdentity
public import InferenceProof.PPDA.Branching
public import InferenceProof.PPDA.TreeSum

set_option linter.style.header false

/-! # The finite program transition table and its polynomial semantics -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {S : Signature}

def Replacement.map {α β : Type*} (f : α → β) : Replacement α → Replacement β
  | .pop => .pop
  | .one X => .one (f X)
  | .two X Y => .two (f X) (f Y)

theorem Replacement.word_map {α β : Type*} (f : α → β) (w : Replacement α) :
    (w.map f).word = w.word.map f := by cases w <;> rfl

/-- All enabled rule instances at a head. -/
structure Branch (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) where
  choice : Bool
  move : Move S
  enabled : headMove E P c X choice = some move

theorem Branch.ext {E : ExprInterpretation S} {P : Program S} {c : Control S}
    {X : StackSymbol S} (a b : Branch E P c X) (h : a.choice = b.choice) : a = b := by
  cases a with
  | mk ba ma ha =>
    cases b with
    | mk bb mb hb =>
      dsimp only at h
      subst bb
      have hm : ma = mb := Option.some.inj (ha.symm.trans hb)
      subst mb
      rfl

noncomputable instance (E : ExprInterpretation S) (P : Program S) (c : Control S)
    (X : StackSymbol S) : Fintype (Branch E P c X) :=
  Fintype.ofInjective Branch.choice (fun a b h => Branch.ext a b h)

/-- The canonical admissible suffix used to establish properties of a local rule. -/
def baseTail : StackSymbol S → List (StackSymbol S)
  | .bottom => []
  | _ => [.bottom]

theorem boundary_baseTail (X : StackSymbol S) : Boundary X (baseTail X) := by
  cases X <;> simp [Boundary, baseTail]

theorem Branch.probability_nonnegative {E : ExprInterpretation S} {P : Program S}
    {c : Control S} {X : StackSymbol S} (edge : Branch E P c X) : 0 ≤ edge.move.probability :=
  (headMove_step E P c X edge.choice edge.move edge.enabled (baseTail X)
    (boundary_baseTail X)).probability_nonnegative

/-- Lift an entire replacement word into the proved finite frame alphabet. -/
def liftReplacement (U : Finset (Code S)) (w : Replacement (StackSymbol S))
    (h : ∀ X ∈ w.word, GoodSymbol U X) : Replacement (FiniteSymbol U) :=
  match w with
  | .pop => .pop
  | .one X => .one ⟨X, h X (by simp [Replacement.word])⟩
  | .two X Y => .two ⟨X, h X (by simp [Replacement.word])⟩
      ⟨Y, h Y (by simp [Replacement.word])⟩

theorem raw_liftReplacement (U : Finset (Code S)) (w : Replacement (StackSymbol S))
    (h : ∀ X ∈ w.word, GoodSymbol U X) :
    (liftReplacement U w h).map Subtype.val = w := by cases w <;> rfl

variable (E : ExprInterpretation S) (P : Program S) (C : Stmt S)

abbrev ProgramControl := FiniteControl (codeSet P C)
abbrev ProgramSymbol := FiniteSymbol (codeSet P C)

abbrev ProgramBranch (c : ProgramControl P C) (X : ProgramSymbol P C) :=
  Branch E P (rawControl c) X.1

noncomputable def branchTarget {c : ProgramControl P C} {X : ProgramSymbol P C}
    (edge : ProgramBranch E P C c X) : ProgramControl P C :=
  (⟨edge.move.target.1, (headMove_closed E P C (rawControl c) X.1 edge.choice edge.move
    c.1.2 X.2 edge.enabled).1⟩, edge.move.target.2)

noncomputable def branchReplacement {c : ProgramControl P C} {X : ProgramSymbol P C}
    (edge : ProgramBranch E P C c X) : Replacement (ProgramSymbol P C) :=
  liftReplacement (codeSet P C) edge.move.replacement
    (headMove_closed E P C (rawControl c) X.1 edge.choice edge.move
      c.1.2 X.2 edge.enabled).2

/-- A local rule with prescribed target control and replacement word. -/
abbrev ProgramEdge (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) :=
  {edge : ProgramBranch E P C c X //
    branchTarget E P C edge = r ∧ branchReplacement E P C edge = w}

noncomputable instance (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) :
    Fintype (ProgramEdge E P C c X r w) := by
  classical
  exact inferInstanceAs (Fintype {edge : ProgramBranch E P C c X //
    branchTarget E P C edge = r ∧ branchReplacement E P C edge = w})

/-- The exact rational transition coefficient obtained from enabled rules. -/
noncomputable def programTransition (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) : ℚ :=
  ∑ edge : ProgramEdge E P C c X r w, edge.1.move.probability

/-- Nonnegativity is derived from the actual operational transition rules. -/
theorem programTransition_nonnegative (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) :
    0 ≤ programTransition E P C c X r w :=
  Finset.sum_nonneg fun edge _ => edge.1.probability_nonnegative

/-- The corresponding nonnegative extended-real coefficient. -/
noncomputable def programWeight (c : ProgramControl P C) (X : ProgramSymbol P C)
    (r : ProgramControl P C) (w : Replacement (ProgramSymbol P C)) : ℝ≥0∞ :=
  ENNReal.ofReal (programTransition E P C c X r w : ℝ)

/-- Program termination based on the finite head-variable polynomial system. -/
noncomputable def polynomialTermination (σ₀ σ : Valuation S) : ℝ≥0∞ :=
  leastSolution (programWeight E P C)
    (⟨compile C .done, locations_subset_codeSet P C (compile_mem_locations C .done)⟩, σ₀)
    ⟨.bottom, trivial⟩ (⟨.done, done_mem_codeSet P C⟩, σ)

end InferenceProof.PPDA
