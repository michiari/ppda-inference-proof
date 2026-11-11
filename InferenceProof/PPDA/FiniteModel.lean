module

public import InferenceProof.PPDA.HeadMachine
public import Mathlib.Data.Fintype.Pi

set_option linter.style.header false

/-!
# Finite program controls and frame symbols

The carriers here are constructed from the finite code closure and value domain.
No finiteness assumption about reachable configurations or program locations is
added to the equivalence theorem.
-/

@[expose] public section

namespace InferenceProof.PPDA

variable {S : Signature}

def valuationEquiv : Valuation S ≃ Option (Store S) where
  toFun v := match v with | .normal σ => some σ | .error => none
  invFun v := match v with | some σ => .normal σ | none => .error
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

noncomputable instance : Fintype (Valuation S) :=
  Fintype.ofEquiv (Option (Store S)) valuationEquiv.symm

/-- A frame records a valid continuation and, for queries, the valid retry site. -/
def GoodSymbol (U : Finset (Code S)) : StackSymbol S → Prop
  | .bottom => True
  | .function k _ _ => k ∈ U
  | .query x f k _ => k ∈ U ∧ Code.seq (.stmt (.sampleQuery x f)) k ∈ U

abbrev FiniteControl (U : Finset (Code S)) := ↥U × Valuation S
abbrev FiniteSymbol (U : Finset (Code S)) := {X : StackSymbol S // GoodSymbol U X}

def rawControl {U : Finset (Code S)} (c : FiniteControl U) : Control S := (c.1.1, c.2)

abbrev SymbolEncoding (U : Finset (Code S)) :=
  Unit ⊕ ((↥U × Var S × Store S) ⊕ (↥U × Var S × FunctionName S × Store S))

def encodeSymbol (U : Finset (Code S)) : FiniteSymbol U → SymbolEncoding U
  | ⟨.bottom, _⟩ => .inl ()
  | ⟨.function k x σ, h⟩ => .inr (.inl (⟨k, h⟩, x, σ))
  | ⟨.query x f k σ, h⟩ => .inr (.inr (⟨k, h.1⟩, x, f, σ))

def decodeSymbol (U : Finset (Code S)) : SymbolEncoding U → StackSymbol S
  | .inl _ => .bottom
  | .inr (.inl (k, x, σ)) => .function k.1 x σ
  | .inr (.inr (k, x, f, σ)) => .query x f k.1 σ

theorem decode_encodeSymbol (U : Finset (Code S)) (X : FiniteSymbol U) :
    decodeSymbol U (encodeSymbol U X) = X.1 := by
  rcases X with ⟨X, h⟩
  cases X <;> rfl

noncomputable instance (U : Finset (Code S)) : Fintype (FiniteSymbol U) :=
  Fintype.ofInjective (encodeSymbol U) (fun a b h => Subtype.ext (by
    simpa only [decode_encodeSymbol] using congrArg (decodeSymbol U) h))

/-- The stack is empty or has exactly one bottom marker, at its end. -/
inductive Grounded : List (StackSymbol S) → Prop where
  | empty : Grounded []
  | bottom : Grounded [.bottom]
  | function {k x σ tail} (grounded : Grounded tail) (nonempty : tail ≠ []) :
      Grounded (.function k x σ :: tail)
  | query {x f k σ tail} (grounded : Grounded tail) (nonempty : tail ≠ []) :
      Grounded (.query x f k σ :: tail)

theorem Grounded.boundary {X : StackSymbol S} {tail : List (StackSymbol S)}
    (h : Grounded (X :: tail)) : Boundary X tail := by
  cases h with
  | bottom => rfl
  | function _ hn => exact hn
  | query _ hn => exact hn

theorem step_grounded {E : ExprInterpretation S} {P : Program S}
    {source target : InferenceProof.Configuration S} {p : ℚ}
    (step : Step E P source p target) (h : Grounded source.stack) : Grounded target.stack := by
  cases step with
  | term | err => exact .empty
  | seqCall => exact .function h (List.cons_ne_nil _ _)
  | seqQuery => exact .query h (List.cons_ne_nil _ _)
  | returnValue | endQuery | errUnwind | errReject => cases h; assumption
  | _ => exact h

/-- All targets and newly pushed frames of the local evaluator stay in the finite carriers. -/
theorem headMove_closed (E : ExprInterpretation S) (P : Program S) (C : Stmt S)
    (c : Control S) (X : StackSymbol S) (branch : Bool) (m : Move S)
    (hc : c.1 ∈ codeSet P C) (hx : GoodSymbol (codeSet P C) X)
    (hm : headMove E P c X branch = some m) :
    m.target.1 ∈ codeSet P C ∧ ∀ Y ∈ m.replacement.word, GoodSymbol (codeSet P C) Y := by
  classical
  have hl := codeSet_closed P C c.1 hc
  rcases c with ⟨code, state⟩
  cases state with
  | error =>
    cases X with
    | bottom =>
      rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
      exact ⟨done_mem_codeSet P C, by simp [Replacement.word]⟩
    | function k x σ =>
      rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
      exact ⟨hc, by simp [Replacement.word]⟩
    | query x f k σ =>
      rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
      exact ⟨hx.2, by simp [Replacement.word]⟩
  | normal σ =>
    cases code with
    | done =>
      cases X with
      | bottom =>
        rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
        exact ⟨done_mem_codeSet P C, by simp [Replacement.word]⟩
      | _ => change none = some m at hm; cases hm
    | ret out =>
      cases X with
      | function k x saved =>
        rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
        exact ⟨hx, by simp [Replacement.word]⟩
      | _ => change none = some m at hm; cases hm
    | endQuery =>
      cases X with
      | query x f k saved =>
        rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
        exact ⟨hx.1, by simp [Replacement.word]⟩
      | _ => change none = some m at hm; cases hm
    | stmt => cases hl
    | seq first k =>
      cases first with
      | stmt s =>
        cases s with
        | assign x e =>
          rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
          exact ⟨hl, by simpa [Replacement.word] using hx⟩
        | skip =>
          rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
          exact ⟨hl, by simpa [Replacement.word] using hx⟩
        | observe =>
          rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
          exact ⟨hl, by simpa [Replacement.word] using hx⟩
        | randomAssign x a n d b =>
          by_cases hv : ValidProbability E σ n d
          · cases branch <;> simp only [headMove, hv, ite_true, ite_false,
              Bool.false_eq_true, Option.some.injEq] at hm
            all_goals cases hm; exact ⟨hl, by simpa [Replacement.word] using hx⟩
          · simp only [headMove, hv, ite_false, reduceCtorEq] at hm
        | ite b t e =>
          by_cases hg : (b.eval E σ).val = 0
          · simp only [headMove, hg, ite_true] at hm
            rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
            exact ⟨hl.2.2, by simpa [Replacement.word] using hx⟩
          · simp only [headMove, hg, ite_false] at hm
            rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
            exact ⟨hl.2.1, by simpa [Replacement.word] using hx⟩
        | «while» b body =>
          by_cases hg : (b.eval E σ).val = 0
          · simp only [headMove, hg, ite_true] at hm
            rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
            exact ⟨hl.1, by simpa [Replacement.word] using hx⟩
          · simp only [headMove, hg, ite_false] at hm
            rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
            exact ⟨hl.2, by simpa [Replacement.word] using hx⟩
        | call x f =>
          rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
          refine ⟨body_locations_subset_codeSet P C f (compile_mem_locations _ _), ?_⟩
          simpa [Replacement.word, GoodSymbol, LocalClosed] using And.intro hl hx
        | sampleQuery x f =>
          rcases single_eq_some.mp hm with ⟨rfl, rfl⟩
          refine ⟨queryCall_mem_codeSet P C x f, ?_⟩
          simpa [Replacement.word, GoodSymbol, LocalClosed] using And.intro (And.intro hl hc) hx
        | seq => cases hl
      | _ => cases hl

end InferenceProof.PPDA
