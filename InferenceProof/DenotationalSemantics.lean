module

public import InferenceProof.OperationalSemantics
public import Mathlib.Logic.Function.Iterate

set_option linter.style.header false

/-!
# Denotational semantics of cpGCL

Definitions from Section 5 of `paper/5-denotational.tex`. We work in the ambient
space of nonnegative mass functions, as in the operational semantics, and define
the subdistribution and linearity predicates separately. This avoids requiring
closure, continuity, or fixed-point proofs merely to state the semantics.

Both fixed-point constructions are defined by the paper's pointwise suprema of
finite iterates from zero. Their fixed-point and leastness properties, as well
as preservation of subdistributions, remain to be proved. Recursive queries use
the joint rejection-loop functional Ψ, not normalization at each finite iterate.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Denotational

noncomputable section

/-- Ambient nonnegative mass functions, ordered pointwise. -/
abbrev Mass (α : Type*) := α → ℝ≥0∞

/-- The total mass `|p|`; missing mass represents divergence. -/
def totalMass {α : Type*} (p : Mass α) : ℝ≥0∞ := ∑' a, p a

/-- The paper's subdistribution condition. Nonnegativity is supplied by `ℝ≥0∞`. -/
def IsSubdistribution {α : Type*} (p : Mass α) : Prop := totalMass p ≤ 1

/-- The space `𝒟(α)`; no closure proofs are bundled into the transformers below. -/
def Subdistribution (α : Type*) := {p : Mass α // IsSubdistribution p}

open scoped Classical in
/-- The point mass `δ_a`, also the paper's embedding `φ(a)`. -/
def dirac {α : Type*} (a : α) : Mass α := fun b => if a = b then 1 else 0

/-- Weighted composition of mass functions and kernels. -/
def bind {α β : Type*} (p : Mass α) (kernel : α → Mass β) : Mass β :=
  fun b => ∑' a, p a * kernel a b

/-- Push a mass function forward along a map, summing coincident outputs. -/
def map {α β : Type*} (f : α → β) (p : Mass α) : Mass β :=
  bind p (fun a => dirac (f a))

variable {S : Signature}

/-- The common output domain `𝕆 = [M] ∪ {err}`; `none` denotes error. -/
abbrev Outcome (S : Signature) := Option (Value S)

abbrev StoreMass (S : Signature) := Mass (Valuation S)
abbrev OutputMass (S : Signature) := Mass (Outcome S)
abbrev Transformer (S : Signature) := StoreMass S → StoreMass S
abbrev FunctionKernel (S : Signature) := Valuation S → OutputMass S

/-- Read a variable, including the error outcome at the error store. -/
def read (x : Var S) : Valuation S → Outcome S
  | .normal σ => some (σ x)
  | .error => none

/-- The marginal `Marg_x(p)`, including its observation-failure mass. -/
def marginal (x : Var S) (p : StoreMass S) : OutputMass S := map (read x) p

/-- Restrict to normal stores whose guard has the requested C-style truth value.
This is restriction, without normalization; both restrictions discard error mass.
-/
def restrict (E : ExprInterpretation S) (guard : Expr S) (truth : Bool)
    (p : StoreMass S) : StoreMass S
  | .normal σ => if decide ((guard.eval E σ).val ≠ 0) = truth then p (.normal σ) else 0
  | .error => 0

/-- The summand `p(σ_err) · δ_{σ_err}`, kept separately in branching and loops. -/
def errorPart (p : StoreMass S) : StoreMass S :=
  fun σ => p .error * dirac .error σ

/-- The transformer maps subdistributions to subdistributions. -/
def PreservesSubdistributions (transform : Transformer S) : Prop :=
  ∀ p, IsSubdistribution p → IsSubdistribution (transform p)

/-- Linearity in the paper's delta-expansion formulation (Section 5, `LinOp`). -/
def IsLinear (transform : Transformer S) : Prop :=
  ∀ p, IsSubdistribution p →
    transform p = fun σ' => ∑' σ, p σ * transform (dirac σ) σ'

/-- The paper's space of linear subdistribution transformers, as a subtype. -/
def LinOp (S : Signature) :=
  {transform : Transformer S // PreservesSubdistributions transform ∧ IsLinear transform}

/-- Deterministic assignment, leaving error input unchanged. -/
def assign (E : ExprInterpretation S) (x : Var S) (e : Expr S) : Transformer S :=
  fun p => bind p fun
    | .normal σ => dirac (.normal (σ.update x (e.eval E σ)))
    | .error => dirac .error

open scoped Classical in
/-- Random assignment with exact rational branch probabilities embedded into `ℝ≥0∞`.
For invalid probabilities the normal-store row is zero, matching the absence of
operational transitions. The paper only defines this clause when every normal
store has a valid probability; `ValidProbabilities` below records that domain.
-/
def randomAssign (E : ExprInterpretation S) (x : Var S)
    (left numerator denominator right : Expr S) : Transformer S :=
  fun p => bind p fun
    | .error => dirac .error
    | .normal σ =>
        if ValidProbability E σ numerator denominator then
          fun σ' =>
            ENNReal.ofReal (branchProbability E σ numerator denominator : ℝ) *
                dirac (.normal (σ.update x (left.eval E σ))) σ' +
              ENNReal.ofReal ((1 - branchProbability E σ numerator denominator : ℚ) : ℝ) *
                dirac (.normal (σ.update x (right.eval E σ))) σ'
        else 0

/-- An unconditional observation violation sends all input mass to the error store. -/
def observe (p : StoreMass S) : StoreMass S :=
  fun σ => totalMass p * dirac .error σ

/-- Ordinary function assignment (equation `eq:sem-func-asgmt`).
The function's intermediate stores are discarded; only its output updates the
original caller store. An error output propagates to the error store.
-/
def functionAssign (x : Var S) (callee : FunctionKernel S) : Transformer S :=
  fun p => bind p fun
    | .error => dirac .error
    | .normal σ => bind (callee (.normal σ)) fun
        | some value => dirac (.normal (σ.update x value))
        | none => dirac .error

/-- Sample-query assignment (equation `eq:sem-sq-asgmt`).
Only successful output values are copied back; the query kernel is β, without
additional normalization at the assignment site. Error input remains error.
-/
def sampleQueryAssign (x : Var S) (query : FunctionKernel S) : Transformer S :=
  fun p => bind p fun
    | .error => dirac .error
    | .normal σ => fun σ' =>
        ∑' value : Value S,
          query (.normal σ) (some value) * dirac (.normal (σ.update x value)) σ'

/-- Recover the output kernel of a function from its body transformer
(`Marg_out ∘ ⟦body⟧ ∘ φ`, equation `eq:sem-func`).
-/
def functionFromBody (out : Var S) (body : Transformer S) : FunctionKernel S :=
  fun σ => marginal out (body (dirac σ))

open scoped Classical in
/-- The normalization `𝒩` of equation `eq:sem-sq`.
The denominator is `1 - q(err)`, not the successful termination mass, so divergence
is retained. An almost-surely rejected query yields zero. The otherwise branch
also makes this definition total outside the subdistribution domain.
-/
def normalize (q : OutputMass S) : OutputMass S :=
  if q none < 1 then
    fun
      | some value => q (some value) / (1 - q none)
      | none => 0
  else 0

/-- The illustrative nonrecursive query definition `𝒩 ∘ ⟦f⟧`.
For recursive queries the definition is the β component of the joint supremum;
its equality with this normalization is a later theorem, not an assumption.
-/
def queryFromFunction (callee : FunctionKernel S) : FunctionKernel S :=
  fun σ => normalize (callee σ)

/-- One rejection retry: `x ↦ Σ_{o ≠ err} q(o) δ_o + q(err) x`
(equation `eq:N-fix-point` and the query component of Ψ).
-/
def rejectionFunctional (q retry : OutputMass S) : OutputMass S :=
  fun outcome => (match outcome with | some value => q (some value) | none => 0) +
    q none * retry outcome

/-- The loop functional `Φ(τ)(p) = p|¬b + τ(body(p|b)) + p(err) δ_err`. -/
def whileFunctional (E : ExprInterpretation S) (guard : Expr S)
    (body continuation : Transformer S) : Transformer S :=
  fun p => restrict E guard false p +
    continuation (body (restrict E guard true p)) + errorPart p

/-- The finite loop iterate `Φ^k(0)`. -/
def whileApproximation (E : ExprInterpretation S) (guard : Expr S)
    (body : Transformer S) (k : ℕ) : Transformer S :=
  (whileFunctional E guard body)^[k] ⊥

/-- The pointwise Kleene supremum defining the loop semantics.
No fixed-point, leastness, or continuity theorem is asserted here.
-/
def whileSemantics (E : ExprInterpretation S) (guard : Expr S)
    (body : Transformer S) : Transformer S :=
  ⨆ k : ℕ, whileApproximation E guard body k

/-- One output kernel per function; the finite function index is shared with syntax. -/
abbrev FunctionFamily (S : Signature) := FunctionName S → FunctionKernel S

/-- The `2n` components `(α, β)` of the recursive environment.
Pointwise order, zero, and suprema are inherited from functions and products.
-/
abbrev Environment (S : Signature) := FunctionFamily S × FunctionFamily S

/-- The auxiliary semantics `⟨C⟩_{α,β}` for every source construct. -/
def auxiliarySemantics (E : ExprInterpretation S) (env : Environment S) :
    Stmt S → Transformer S
  | .assign x e => assign E x e
  | .randomAssign x left numerator denominator right =>
      randomAssign E x left numerator denominator right
  | .call x f => functionAssign x (env.1 f)
  | .sampleQuery x f => sampleQueryAssign x (env.2 f)
  | .ite guard thenBranch elseBranch => fun p =>
      auxiliarySemantics E env thenBranch (restrict E guard true p) +
        auxiliarySemantics E env elseBranch (restrict E guard false p) + errorPart p
  | .while guard body => whileSemantics E guard (auxiliarySemantics E env body)
  | .observe => observe
  | .skip => id
  | .seq first rest => auxiliarySemantics E env rest ∘ auxiliarySemantics E env first

/-- The simultaneous recursion functional Ψ (equation `eq:opfunc`).
The new α interprets the bodies using the old `(α,β)`. The new β uses the old α
and β in the affine rejection equation, preserving the paper's iteration order.
-/
def recursionFunctional (E : ExprInterpretation S) (P : Program S)
    (env : Environment S) : Environment S :=
  (fun f => functionFromBody (P.functions f).out
      (auxiliarySemantics E env (P.functions f).body),
    fun f σ => rejectionFunctional (env.1 f σ) (env.2 f σ))

/-- The finite joint recursion iterate `(α_k,β_k) = Ψ^k(0,0)`. -/
def recursionApproximation (E : ExprInterpretation S) (P : Program S)
    (k : ℕ) : Environment S :=
  (recursionFunctional E P)^[k] ⊥

/-- The pointwise Kleene supremum `(α*,β*)` defining recursive calls and queries.
Its characterization as the least fixed point is reserved for the proof stage.
-/
def recursiveEnvironment (E : ExprInterpretation S) (P : Program S) : Environment S :=
  ⨆ k : ℕ, recursionApproximation E P k

/-- The denotation `⟦f_i(x_i,1, ..., x_i,n_i)⟧ = α*_i`. -/
def functionSemantics (E : ExprInterpretation S) (P : Program S)
    (f : FunctionName S) : FunctionKernel S :=
  (recursiveEnvironment E P).1 f

/-- The denotation `⟦sample-query f_i(...)⟧ = β*_i`. -/
def sampleQuerySemantics (E : ExprInterpretation S) (P : Program S)
    (f : FunctionName S) : FunctionKernel S :=
  (recursiveEnvironment E P).2 f

/-- The full source-fragment denotation `⟦C⟧`, a mass transformer. -/
def semantics (E : ExprInterpretation S) (P : Program S) (C : Stmt S) : Transformer S :=
  auxiliarySemantics E (recursiveEnvironment E P) C

/-- Fragment semantics on an initial point mass, for comparison with `ℙ_{C,σ₀}`. -/
def fragmentSemantics (E : ExprInterpretation S) (P : Program S)
    (C : Stmt S) (σ₀ : Valuation S) : StoreMass S :=
  semantics E P C (dirac σ₀)

/-- Whole-program entry matching the ordinary call of operational Section 4.2. -/
def programSemantics (E : ExprInterpretation S) (P : Program S) : StoreMass S :=
  fragmentSemantics E P (.call P.dummy P.main) (.normal Store.zero)

/-- Whole-program entry through a query to main, as described in Section 3. -/
def queryProgramSemantics (E : ExprInterpretation S) (P : Program S) : StoreMass S :=
  fragmentSemantics E P (.sampleQuery P.dummy P.main) (.normal Store.zero)

/-- The paper requires every random-assignment ratio to be valid at every normal
store. Calls are checked through the function table by `ValidProgramProbabilities`.
-/
def ValidProbabilities (E : ExprInterpretation S) : Stmt S → Prop
  | .randomAssign _ _ numerator denominator _ =>
      ∀ σ, ValidProbability E σ numerator denominator
  | .ite _ thenBranch elseBranch =>
      ValidProbabilities E thenBranch ∧ ValidProbabilities E elseBranch
  | .while _ body => ValidProbabilities E body
  | .seq first rest => ValidProbabilities E first ∧ ValidProbabilities E rest
  | _ => True

/-- The random-probability side condition for all function definitions in a program. -/
def ValidProgramProbabilities (E : ExprInterpretation S) (P : Program S) : Prop :=
  ∀ f, ValidProbabilities E (P.functions f).body

end

end InferenceProof.Denotational
