module

public import InferenceProof.PPDA.HeadMachine

set_option linter.style.header false

/-! # Rule instances are determined by their Boolean branch choice -/

@[expose] public section

namespace InferenceProof.PPDA

variable {S : Signature} (E : ExprInterpretation S) (P : Program S)

abbrev PrimitiveEdge (s : Stmt S) (σ : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) :=
  Σ p : ℚ, Σ next : Code S, Σ σ' : Store S,
    Step E P ⟨.stmt s, .normal σ, X :: tail⟩ p ⟨next, .normal σ', X :: tail⟩

theorem primitiveEdge_ext (s : Stmt S) (σ : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (a b : PrimitiveEdge E P s σ X tail)
    (h : stepBranch a.2.2.2 = stepBranch b.2.2.2) : a = b := by
  rcases a with ⟨pa, ca, σa, a⟩
  rcases b with ⟨pb, cb, σb, b⟩
  cases a <;> cases b <;>
    simp_all only [stepBranch, Sigma.mk.injEq, heq_eq_eq, true_and, Bool.false_eq_true,
      Bool.true_eq_false] <;> contradiction

theorem primitiveEdge_notCall (s : Stmt S) (σ : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (a : PrimitiveEdge E P s σ X tail) :
    ¬ (Code.stmt s).IsCallOrQuery := by
  rcases a with ⟨p, next, σ', step⟩
  cases step <;> simp only [Code.IsCallOrQuery, not_false_eq_true]

abbrev FullEdge (c : InferenceProof.Configuration S) :=
  Σ p : ℚ, Σ target : InferenceProof.Configuration S, Step E P c p target

open scoped Classical in
noncomputable def liftPrimitive (s : Stmt S) (σ : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (k : Code S) (e : PrimitiveEdge E P s σ X tail) :
    FullEdge E P ⟨.seq (.stmt s) k, .normal σ, X :: tail⟩ :=
  if h : e.2.1 = .done then
    ⟨e.1, ⟨k, .normal e.2.2.1, X :: tail⟩,
      .seqEnd (h ▸ e.2.2.2)⟩
  else
    ⟨e.1, ⟨e.2.1.append k, .normal e.2.2.1, X :: tail⟩,
      .seqCont e.2.2.2 (primitiveEdge_notCall E P s σ X tail e) h⟩

theorem liftPrimitive_cont (s : Stmt S) (σ σ' : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (k next : Code S) {p : ℚ}
    (inner : Step E P ⟨.stmt s, .normal σ, X :: tail⟩ p ⟨next, .normal σ', X :: tail⟩)
    (hn : ¬ (Code.stmt s).IsCallOrQuery) (hd : next ≠ .done) :
    liftPrimitive E P s σ X tail k ⟨p, next, σ', inner⟩ =
      ⟨p, ⟨next.append k, .normal σ', X :: tail⟩, .seqCont inner hn hd⟩ := by
  simp only [liftPrimitive, hd, ↓reduceDIte]

theorem liftPrimitive_end (s : Stmt S) (σ σ' : Store S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (k : Code S) {p : ℚ}
    (inner : Step E P ⟨.stmt s, .normal σ, X :: tail⟩ p ⟨.done, .normal σ', X :: tail⟩) :
    liftPrimitive E P s σ X tail k ⟨p, .done, σ', inner⟩ =
      ⟨p, ⟨k, .normal σ', X :: tail⟩, .seqEnd inner⟩ := by
  simp only [liftPrimitive, ↓reduceDIte]

/-- No two distinct outgoing rule instances have the same branch identifier. -/
theorem fullEdge_ext (U : Finset (Code S)) (c : Control S) (X : StackSymbol S)
    (tail : List (StackSymbol S)) (hc : LocalClosed U c.1)
    (a b : FullEdge E P ⟨c.1, c.2, X :: tail⟩)
    (h : stepBranch a.2.2 = stepBranch b.2.2) : a = b := by
  rcases c with ⟨code, state⟩
  rcases a with ⟨pa, ta, a⟩
  rcases b with ⟨pb, tb, b⟩
  cases state with
  | error => cases a <;> cases b <;> rfl
  | normal σ =>
    cases code with
    | done => cases a; cases b; rfl
    | ret out => cases a; cases b; rfl
    | endQuery => cases a; cases b; rfl
    | stmt => cases hc
    | seq first k =>
      cases first with
      | stmt s =>
        cases a with
        | seqCont ai an ad =>
          cases b with
          | seqCont bi bn bd =>
            have hi := primitiveEdge_ext E P s σ X tail ⟨_, _, _, ai⟩ ⟨_, _, _, bi⟩ h
            simpa only [liftPrimitive, ad, bd, ↓reduceDIte] using
              congrArg (liftPrimitive E P s σ X tail k) hi
          | seqEnd bi =>
            have hi := primitiveEdge_ext E P s σ X tail ⟨_, _, _, ai⟩ ⟨_, _, _, bi⟩ h
            exact False.elim (ad (congrArg (fun e => e.2.1) hi))
          | seqCall => cases ai
          | seqQuery => cases ai
          | observe => cases ai
        | seqEnd ai =>
          cases b with
          | seqCont bi bn bd =>
            have hi := primitiveEdge_ext E P s σ X tail ⟨_, _, _, ai⟩ ⟨_, _, _, bi⟩ h
            exact False.elim (bd (congrArg (fun e => e.2.1) hi).symm)
          | seqEnd bi =>
            have hi := primitiveEdge_ext E P s σ X tail ⟨_, _, _, ai⟩ ⟨_, _, _, bi⟩ h
            simpa only [liftPrimitive_end] using congrArg (liftPrimitive E P s σ X tail k) hi
          | seqCall => cases ai
          | seqQuery => cases ai
          | observe => cases ai
        | seqCall => cases b <;> first | rfl | rename_i inner; cases inner
        | seqQuery => cases b <;> first | rfl | rename_i inner; cases inner
        | observe => cases b <;> first | rfl | rename_i inner; cases inner
      | _ => cases hc

end InferenceProof.PPDA
