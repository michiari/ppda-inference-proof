module

public import InferenceProof.SemanticsCommon
public import Mathlib.Logic.Relation
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option linter.style.header false

/-!
# Operational semantics of cpGCL

The rules below follow Section 4, Figure `fig:op-semantics` in
`paper/4-operational.tex`. `Step` retains rule derivations as data so that
different random branches leading to the same configuration are counted
separately. Transition weights and termination probabilities sum these weights.

The runtime code includes the paper's auxiliary `↓`, `return`, and `endquery`.
`Code.append` implements the paper's right-associative sequencing convention.
Calls start from the current store; return restores the caller's saved store
and updates only the target variable. No additional parameter copying or
local-variable initialization is inserted into the paper's call rule.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof

/-- Runtime fragments. Source sequencing is expanded by `Code.ofStmt`. -/
inductive Code (S : Signature) where
  | done
  | stmt (statement : Stmt S)
  | seq (first rest : Code S)
  | ret (out : Var S)
  | endQuery

/-- Concatenate fragments, reassociating to the right and removing a leading `↓`.
The final continuation is retained even when it is `↓`, so a final call or
observation has the sequenced form required by the operational rules.
-/
def Code.append {S : Signature} : Code S → Code S → Code S
  | .done, rest => rest
  | .seq first rest, continuation => .seq first (rest.append continuation)
  | first, rest => .seq first rest

/-- Embed source code, normalizing sequencing. Branches are embedded when entered. -/
def Code.ofStmt {S : Signature} : Stmt S → Code S
  | .seq first rest => (ofStmt first).append (ofStmt rest)
  | statement => .stmt statement

/-- The exclusion in the premise of `seq-cont`. -/
def Code.IsCallOrQuery {S : Signature} : Code S → Prop
  | .stmt (.call _ _) => True
  | .stmt (.sampleQuery _ _) => True
  | _ => False

/-- Stack symbols `[C,r,σ]`, `(x_r = f_i(...); C,σ)`, and `Z₀`. -/
inductive StackSymbol (S : Signature) where
  | function (continuation : Code S) (target : Var S) (saved : Store S)
  | query (target : Var S) (callee : FunctionName S)
      (continuation : Code S) (saved : Store S)
  | bottom

/-- The head of the stack list is its top; the empty stack signals termination. -/
structure Configuration (S : Signature) where
  code : Code S
  store : Valuation S
  stack : List (StackSymbol S)

variable {S : Signature}

/-- A single probability-labelled rule derivation `⟨C,σ,G⟩ ⊢_p ⟨C',σ',G'⟩`.

Ordinary rules require normal stores and nonempty stacks. Only `term` and `err`
empty the stack. The family lives in `Type`, rather than `Prop`, to distinguish
the two random-assignment derivations even if their weights and endpoints agree.
-/
inductive Step (E : ExprInterpretation S) (P : Program S) :
    Configuration S → ℚ → Configuration S → Type where
  | skip {σ γ G} :
      Step E P ⟨.stmt .skip, .normal σ, γ :: G⟩ 1 ⟨.done, .normal σ, γ :: G⟩
  | term {σ} :
      Step E P ⟨.done, .normal σ, [.bottom]⟩ 1 ⟨.done, .normal σ, []⟩
  | detAssign {σ γ G x e} :
      Step E P ⟨.stmt (.assign x e), .normal σ, γ :: G⟩ 1
        ⟨.done, .normal (σ.update x (e.eval E σ)), γ :: G⟩
  | rndAssignLeft {σ γ G x e₁ e₂ e₃ e₄}
      (valid : ValidProbability E σ e₂ e₃) :
      Step E P ⟨.stmt (.randomAssign x e₁ e₂ e₃ e₄), .normal σ, γ :: G⟩
        (branchProbability E σ e₂ e₃)
        ⟨.done, .normal (σ.update x (e₁.eval E σ)), γ :: G⟩
  | rndAssignRight {σ γ G x e₁ e₂ e₃ e₄}
      (valid : ValidProbability E σ e₂ e₃) :
      Step E P ⟨.stmt (.randomAssign x e₁ e₂ e₃ e₄), .normal σ, γ :: G⟩
        (1 - branchProbability E σ e₂ e₃)
        ⟨.done, .normal (σ.update x (e₄.eval E σ)), γ :: G⟩
  | ifThen {σ γ G b C₁ C₂} (guard : (b.eval E σ).val ≠ 0) :
      Step E P ⟨.stmt (.ite b C₁ C₂), .normal σ, γ :: G⟩ 1
        ⟨Code.ofStmt C₁, .normal σ, γ :: G⟩
  | ifElse {σ γ G b C₁ C₂} (guard : (b.eval E σ).val = 0) :
      Step E P ⟨.stmt (.ite b C₁ C₂), .normal σ, γ :: G⟩ 1
        ⟨Code.ofStmt C₂, .normal σ, γ :: G⟩
  | whileCont {σ γ G b C} (guard : (b.eval E σ).val ≠ 0) :
      Step E P ⟨.stmt (.while b C), .normal σ, γ :: G⟩ 1
        ⟨(Code.ofStmt C).append (.stmt (.while b C)), .normal σ, γ :: G⟩
  | whileEnd {σ γ G b C} (guard : (b.eval E σ).val = 0) :
      Step E P ⟨.stmt (.while b C), .normal σ, γ :: G⟩ 1
        ⟨.done, .normal σ, γ :: G⟩
  | seqCont {σ σ' γ G C₁ C₁' C₂ p}
      (step : Step E P ⟨C₁, .normal σ, γ :: G⟩ p ⟨C₁', .normal σ', γ :: G⟩)
      (notCallOrQuery : ¬ C₁.IsCallOrQuery) (notDone : C₁' ≠ .done) :
      Step E P ⟨.seq C₁ C₂, .normal σ, γ :: G⟩ p
        ⟨C₁'.append C₂, .normal σ', γ :: G⟩
  | seqEnd {σ σ' γ G C₁ C₂ p}
      (step : Step E P ⟨C₁, .normal σ, γ :: G⟩ p ⟨.done, .normal σ', γ :: G⟩) :
      Step E P ⟨.seq C₁ C₂, .normal σ, γ :: G⟩ p ⟨C₂, .normal σ', γ :: G⟩
  | seqCall {σ γ G x f C} :
      Step E P ⟨.seq (.stmt (.call x f)) C, .normal σ, γ :: G⟩ 1
        ⟨(Code.ofStmt (P.functions f).body).append (.ret (P.functions f).out),
          .normal σ, .function C x σ :: γ :: G⟩
  | returnValue {σ σ' γ G C x out} :
      Step E P ⟨.ret out, .normal σ, .function C x σ' :: γ :: G⟩ 1
        ⟨C, .normal (σ'.update x (σ out)), γ :: G⟩
  | seqQuery {σ γ G x f C} :
      Step E P ⟨.seq (.stmt (.sampleQuery x f)) C, .normal σ, γ :: G⟩ 1
        ⟨.seq (.stmt (.call x f)) .endQuery, .normal σ, .query x f C σ :: γ :: G⟩
  | endQuery {σ σ' γ G x f C} :
      Step E P ⟨.endQuery, .normal σ, .query x f C σ' :: γ :: G⟩ 1
        ⟨C, .normal σ, γ :: G⟩
  | observe {σ γ G C} :
      Step E P ⟨.seq (.stmt .observe) C, .normal σ, γ :: G⟩ 1
        ⟨C, .error, γ :: G⟩
  | errUnwind {σ γ G C C' x} :
      Step E P ⟨C, .error, .function C' x σ :: γ :: G⟩ 1 ⟨C, .error, γ :: G⟩
  | errReject {σ γ G C C' x f} :
      Step E P ⟨C, .error, .query x f C' σ :: γ :: G⟩ 1
        ⟨.seq (.stmt (.sampleQuery x f)) C', .normal σ, γ :: G⟩
  | err {C} :
      Step E P ⟨C, .error, [.bottom]⟩ 1 ⟨.done, .error, []⟩

/-- Aggregate all rule instances with the same source and target, as in the paper. -/
noncomputable def transitionWeight (E : ExprInterpretation S) (P : Program S)
    (source target : Configuration S) : ℝ≥0∞ :=
  ∑' derivation : (Σ p : ℚ, Step E P source p target),
    ENNReal.ofReal (derivation.1 : ℝ)

/-- A positive-probability transition, for the paper's reachability relation. -/
def PositiveStep (E : ExprInterpretation S) (P : Program S)
    (source target : Configuration S) : Prop :=
  ∃ p : ℚ, 0 < p ∧ Nonempty (Step E P source p target)

/-- Zero or more positive-probability transitions (`⊢_*` in Section 4). -/
def Reachable (E : ExprInterpretation S) (P : Program S) :
    Configuration S → Configuration S → Prop :=
  Relation.ReflTransGen (PositiveStep E P)

/-- Run a source fragment with an explicit final `↓` continuation and stack `Z₀`. -/
def initialFragment (C : Stmt S) (σ : Valuation S) : Configuration S :=
  ⟨(Code.ofStmt C).append .done, σ, [.bottom]⟩

/-- Section 4.2's whole-program entry `dummy = f₀(); ↓` in the zero store.
Section 3 instead describes entry through `sample-query`; `initialQuery` provides
that entry separately rather than identifying the two conventions.
-/
def initialProgram (P : Program S) : Configuration S :=
  initialFragment (.call P.dummy P.main) (.normal Store.zero)

/-- Section 3's entry through sampling the main function's distribution. -/
def initialQuery (P : Program S) : Configuration S :=
  initialFragment (.sampleQuery P.dummy P.main) (.normal Store.zero)

/-- Finite runs retain branch multiplicity and multiply the transition labels. -/
inductive Run (E : ExprInterpretation S) (P : Program S) :
    Configuration S → ℚ → Configuration S → Type where
  | refl (c : Configuration S) : Run E P c 1 c
  | tail {source middle target p q}
      (previous : Run E P source p middle) (step : Step E P middle q target) :
      Run E P source (p * q) target

/-- Total mass of finite terminating runs with the given final store.
Infinite runs contribute no mass. `Equivalence.Main` proves equality with the
denotational semantics and the resulting subdistribution bound.
-/
noncomputable def terminationProbability (E : ExprInterpretation S) (P : Program S)
    (source : Configuration S) (σ : Valuation S) : ℝ≥0∞ :=
  ∑' run : (Σ p : ℚ, Run E P source p ⟨.done, σ, []⟩),
    ENNReal.ofReal (run.1 : ℝ)

/-- The operational semantics `ℙ_{C,σ₀}(σ)` of a source fragment. -/
noncomputable def fragmentSemantics (E : ExprInterpretation S) (P : Program S)
    (C : Stmt S) (σ₀ σ : Valuation S) : ℝ≥0∞ :=
  terminationProbability E P (initialFragment C σ₀) σ

/-- The whole-program operational semantics using the entry in Section 4.2. -/
noncomputable def programSemantics (E : ExprInterpretation S) (P : Program S)
    (σ : Valuation S) : ℝ≥0∞ :=
  terminationProbability E P (initialProgram P) σ

end InferenceProof
