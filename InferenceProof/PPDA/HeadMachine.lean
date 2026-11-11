module

public import InferenceProof.PPDA.CodeClosure
public import InferenceProof.PPDA.Basic
public import InferenceProof.PPDA.OperationalPaths
import Mathlib.Tactic.CasesM

set_option linter.style.header false

/-!
# The program's head transition table

At a compiled location the current control, store, top stack symbol and a single
Boolean branch choice determine the transition. The Boolean distinguishes the
two random-assignment rules even when they have the same probability and result.
-/

@[expose] public section

namespace InferenceProof.PPDA

variable {S : Signature}

abbrev Control (S : Signature) := Code S × Valuation S

structure Move (S : Signature) where
  probability : ℚ
  target : Control S
  replacement : Replacement (StackSymbol S)

/-- Deterministic rules use the false branch only. -/
def single (branch : Bool) (move : Move S) : Option (Move S) :=
  if branch then none else some move

theorem single_eq_some {branch : Bool} {a b : Move S} :
    single branch a = some b ↔ branch = false ∧ a = b := by
  cases branch <;> simp only [single, Bool.false_eq_true, ite_false, Option.some.injEq,
    Bool.true_eq_false, ite_true, reduceCtorEq, false_and, true_and]

open scoped Classical in
/-- The finite branching head evaluator, with no full stack in its input. -/
noncomputable def headMove (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) (branch : Bool) : Option (Move S) :=
  match c.2 with
  | .error => single branch <| match X with
      | .bottom => ⟨1, (.done, .error), .pop⟩
      | .function _ _ _ => ⟨1, (c.1, .error), .pop⟩
      | .query x f k σ => ⟨1, (.seq (.stmt (.sampleQuery x f)) k, .normal σ), .pop⟩
  | .normal σ => match c.1 with
      | .done => match X with
          | .bottom => single branch ⟨1, (.done, .normal σ), .pop⟩
          | _ => none
      | .ret out => match X with
          | .function k x saved => single branch ⟨1, (k, .normal (saved.update x (σ out))), .pop⟩
          | _ => none
      | .endQuery => match X with
          | .query _ _ k _ => single branch ⟨1, (k, .normal σ), .pop⟩
          | _ => none
      | .seq (.stmt s) k => match s with
          | .skip => single branch ⟨1, (k, .normal σ), .one X⟩
          | .assign x e => single branch ⟨1, (k, .normal (σ.update x (e.eval E σ))), .one X⟩
          | .randomAssign x a n d b =>
              if ValidProbability E σ n d then
                if branch then
                  some ⟨1 - branchProbability E σ n d,
                    (k, .normal (σ.update x (b.eval E σ))), .one X⟩
                else some ⟨branchProbability E σ n d,
                    (k, .normal (σ.update x (a.eval E σ))), .one X⟩
              else none
          | .ite b t e =>
              if (b.eval E σ).val = 0 then single branch ⟨1, (compile e k, .normal σ), .one X⟩
              else single branch ⟨1, (compile t k, .normal σ), .one X⟩
          | .while b body =>
              if (b.eval E σ).val = 0 then single branch ⟨1, (k, .normal σ), .one X⟩
              else single branch
                ⟨1, (compile body (.seq (.stmt (.while b body)) k), .normal σ), .one X⟩
          | .call x f => single branch
              ⟨1, (compile (P.functions f).body (.ret (P.functions f).out), .normal σ),
                .two (.function k x σ) X⟩
          | .sampleQuery x f => single branch
              ⟨1, (.seq (.stmt (.call x f)) .endQuery, .normal σ), .two (.query x f k σ) X⟩
          | .observe => single branch ⟨1, (k, .error), .one X⟩
          | .seq _ _ => none
      | _ => none

/-- A bottom head has no suffix; other heads are above a nonempty suffix. -/
def Boundary : StackSymbol S → List (StackSymbol S) → Prop
  | .bottom, tail => tail = []
  | _, tail => tail ≠ []

theorem append_ne_done {a : Code S} (ha : a ≠ .done) (b : Code S) : a.append b ≠ .done := by
  cases a with
  | done => exact False.elim (ha rfl)
  | _ => exact nofun

theorem ofStmt_ne_done (C : Stmt S) : Code.ofStmt C ≠ .done := by
  induction C with
  | seq a b iha ihb => exact append_ne_done iha _
  | _ => exact nofun

/-- The choice distinguishing random assignment's two rule instances. -/
def stepBranch {E : ExprInterpretation S} {P : Program S}
    {source target : InferenceProof.Configuration S} {p : ℚ} :
    Step E P source p target → Bool
  | .rndAssignRight _ => true
  | .seqCont step _ _ => stepBranch step
  | .seqEnd step => stepBranch step
  | _ => false

def castStep {E : ExprInterpretation S} {P : Program S}
    {a b b' : InferenceProof.Configuration S} {p : ℚ} (h : b = b')
    (step : Step E P a p b) : {s : Step E P a p b' // stepBranch s = stepBranch step} := by
  cases h
  exact ⟨step, rfl⟩

/-- Every enabled head transition is an operational step above any admissible suffix. -/
noncomputable def headMove_witness (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) (branch : Bool) (m : Move S)
    (h : headMove E P c X branch = some m) (tail : List (StackSymbol S))
    (hb : Boundary X tail) :
    {step : Step E P ⟨c.1, c.2, X :: tail⟩ m.probability
      ⟨m.target.1, m.target.2, m.replacement.word ++ tail⟩ // stepBranch step = branch} := by
  rcases c with ⟨code, state⟩
  cases state with
  | error =>
    cases X with
    | bottom =>
      rcases single_eq_some.mp h with ⟨rfl, rfl⟩
      subst tail
      exact ⟨.err, rfl⟩
    | function k x σ =>
      rcases single_eq_some.mp h with ⟨rfl, rfl⟩
      cases tail with
      | nil => exact False.elim (hb rfl)
      | cons Y rest => exact ⟨.errUnwind, rfl⟩
    | query x f k σ =>
      rcases single_eq_some.mp h with ⟨rfl, rfl⟩
      cases tail with
      | nil => exact False.elim (hb rfl)
      | cons Y rest => exact ⟨.errReject, rfl⟩
  | normal σ =>
    cases code with
    | done =>
      cases X with
      | bottom =>
        rcases single_eq_some.mp h with ⟨rfl, rfl⟩
        subst tail
        exact ⟨.term, rfl⟩
      | function => change none = some m at h; cases h
      | query => change none = some m at h; cases h
    | ret out =>
      cases X with
      | function k x saved =>
        rcases single_eq_some.mp h with ⟨rfl, rfl⟩
        cases tail with
        | nil => exact False.elim (hb rfl)
        | cons Y rest => exact ⟨.returnValue, rfl⟩
      | bottom => change none = some m at h; cases h
      | query => change none = some m at h; cases h
    | endQuery =>
      cases X with
      | query x f k saved =>
        rcases single_eq_some.mp h with ⟨rfl, rfl⟩
        cases tail with
        | nil => exact False.elim (hb rfl)
        | cons Y rest => exact ⟨.endQuery, rfl⟩
      | bottom => change none = some m at h; cases h
      | function => change none = some m at h; cases h
    | stmt => change none = some m at h; cases h
    | seq first k =>
      cases first with
      | stmt s =>
        cases s with
        | skip =>
          rcases single_eq_some.mp h with ⟨rfl, rfl⟩
          exact ⟨.seqEnd .skip, rfl⟩
        | assign x e =>
          rcases single_eq_some.mp h with ⟨rfl, rfl⟩
          exact ⟨.seqEnd .detAssign, rfl⟩
        | randomAssign x a n d b =>
          by_cases hv : ValidProbability E σ n d
          · cases branch <;> simp only [headMove, hv, ite_true, Bool.false_eq_true,
              ite_false, ite_true, Option.some.injEq] at h
            · cases h; exact ⟨.seqEnd (.rndAssignLeft hv), rfl⟩
            · cases h; exact ⟨.seqEnd (.rndAssignRight hv), rfl⟩
          · simp only [headMove, hv, ite_false, reduceCtorEq] at h
        | ite b t e =>
          by_cases hg : (b.eval E σ).val = 0
          · simp only [headMove, hg, ite_true] at h
            rcases single_eq_some.mp h with ⟨rfl, rfl⟩
            exact ⟨.seqCont (.ifElse hg) (by simp only [Code.IsCallOrQuery, not_false_eq_true])
              (ofStmt_ne_done e), rfl⟩
          · simp only [headMove, hg, ite_false] at h
            rcases single_eq_some.mp h with ⟨rfl, rfl⟩
            exact ⟨.seqCont (.ifThen hg) (by simp only [Code.IsCallOrQuery, not_false_eq_true])
              (ofStmt_ne_done t), rfl⟩
        | «while» b body =>
          by_cases hg : (b.eval E σ).val = 0
          · simp only [headMove, hg, ite_true] at h
            rcases single_eq_some.mp h with ⟨rfl, rfl⟩
            exact ⟨.seqEnd (.whileEnd hg), rfl⟩
          · simp only [headMove, hg, ite_false] at h
            rcases single_eq_some.mp h with ⟨rfl, rfl⟩
            exact castStep
              (b' := ⟨compile body (.seq (.stmt (.while b body)) k), .normal σ, X :: tail⟩)
              (by simp only [compile, append_assoc, Code.append])
              (Step.seqCont (Step.whileCont hg)
                (by simp only [Code.IsCallOrQuery, not_false_eq_true])
                (append_ne_done (ofStmt_ne_done body) _) (C₂ := k) (γ := X) (G := tail))
        | call x f =>
          rcases single_eq_some.mp h with ⟨rfl, rfl⟩
          exact ⟨.seqCall, rfl⟩
        | sampleQuery x f =>
          rcases single_eq_some.mp h with ⟨rfl, rfl⟩
          exact ⟨.seqQuery, rfl⟩
        | observe =>
          rcases single_eq_some.mp h with ⟨rfl, rfl⟩
          exact ⟨.observe, rfl⟩
        | seq => change none = some m at h; cases h
      | _ => change none = some m at h; cases h

noncomputable def headMove_step (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) (branch : Bool) (m : Move S)
    (h : headMove E P c X branch = some m) (tail : List (StackSymbol S))
    (hb : Boundary X tail) :
    Step E P ⟨c.1, c.2, X :: tail⟩ m.probability
      ⟨m.target.1, m.target.2, m.replacement.word ++ tail⟩ :=
  (headMove_witness E P c X branch m h tail hb).1

theorem headMove_step_branch (E : ExprInterpretation S) (P : Program S)
    (c : Control S) (X : StackSymbol S) (branch : Bool) (m : Move S)
    (h : headMove E P c X branch = some m) (tail : List (StackSymbol S))
    (hb : Boundary X tail) :
    stepBranch (headMove_step E P c X branch m h tail hb) = branch :=
  (headMove_witness E P c X branch m h tail hb).2

open scoped Classical in
/-- A primitive normal-store reduction lifted into its surrounding sequence. -/
theorem primitive_headMove (E : ExprInterpretation S) (P : Program S)
    (s : Stmt S) (σ σ' : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (k next : Code S) {p : ℚ}
    (step : Step E P ⟨.stmt s, .normal σ, X :: tail⟩ p
      ⟨next, .normal σ', X :: tail⟩) :
    headMove E P (.seq (.stmt s) k, .normal σ) X (stepBranch step) =
      some ⟨p, (if next = .done then k else next.append k, .normal σ'), .one X⟩ := by
  classical
  cases step <;> simp_all [headMove, stepBranch, single,
    ofStmt_ne_done, append_ne_done, compile, append_assoc, Code.append]

/-- Completeness of the head evaluator at compiled locations. -/
theorem headMove_complete (E : ExprInterpretation S) (P : Program S)
    (U : Finset (Code S)) (c : Control S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) {p : ℚ} {target : InferenceProof.Configuration S}
    (hc : LocalClosed U c.1) (step : Step E P ⟨c.1, c.2, X :: tail⟩ p target) :
    ∃ m, headMove E P c X (stepBranch step) = some m ∧ m.probability = p ∧
      m.target = (target.code, target.store) ∧ m.replacement.word ++ tail = target.stack := by
  classical
  rcases c with ⟨code, state⟩
  cases state with
  | error =>
    cases step <;> simp [headMove, stepBranch, single, Replacement.word]
  | normal σ =>
    cases code with
    | done => cases step; simp [headMove, stepBranch, single, Replacement.word]
    | ret out => cases step; simp [headMove, stepBranch, single, Replacement.word]
    | endQuery => cases step; simp [headMove, stepBranch, single, Replacement.word]
    | stmt => cases hc
    | seq first k =>
      cases first with
      | stmt s =>
        cases step with
        | seqCont inner hn hd =>
          refine ⟨⟨_, _, .one X⟩, ?_, rfl, rfl, rfl⟩
          simpa only [stepBranch, hd, ite_false] using
            primitive_headMove E P s _ _ X tail k _ inner
        | seqEnd inner =>
          refine ⟨⟨_, _, .one X⟩, ?_, rfl, rfl, rfl⟩
          simpa only [stepBranch, ite_true] using
            primitive_headMove E P s _ _ X tail k _ inner
        | seqCall => simp [headMove, stepBranch, single, compile, Replacement.word]
        | seqQuery => simp [headMove, stepBranch, single, Replacement.word]
        | observe => simp [headMove, stepBranch, single, Replacement.word]
      | _ => cases hc

end InferenceProof.PPDA
