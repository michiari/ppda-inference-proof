# inference-proof

Lean 4 definitions for *Exact Inference for Nested Discrete Probabilistic
Programs*, whose sources are in `../paper`. Build with `lake build`; import
`InferenceProof` to use the formalization. There are no theorem proofs or
proof placeholders.

- `InferenceProof/Syntax.lean` defines finite variable, function, and value
  domains; expressions; all source statements; function definitions; and programs
  (Section 3, `paper/3-cprGCL.tex`). `Program.WellFormed` expresses that main is
  `f₀` and has no parameters.
- `InferenceProof/OperationalSemantics.lean` defines stores, expression evaluation,
  runtime code, configurations, and every rule in Figure `fig:op-semantics`
  (Section 4, `paper/4-operational.tex`). It also defines transition weights,
  positive-probability reachability, finite runs, and termination probabilities.
- `InferenceProof/DenotationalSemantics.lean` defines the distribution transformers
  of Section 5 (`paper/5-denotational.tex`) in the namespace
  `InferenceProof.Denotational`: marginals, guard restriction, normalization,
  all statement clauses, and the joint semantics of recursive calls and queries.

Calls carry a target variable and function name. Their argument list is implicit:
it is exactly the callee's `parameters` list, following the restriction in
Section 3 and the explanation in Section 5. The final `return out` is supplied
by the call rule, rather than included in the source body. As in Figure
`fig:op-semantics`, calls enter with the current store, and returns restore the
saved caller store with only the target variable updated. The initial store is
zero; the call rule does not reset other locals.

The paper does not specify a grammar or an overflow policy for arithmetic
operators. `Signature` supplies unary and binary operator symbols;
`ExprInterpretation` supplies their total interpretations on `Fin (M + 1)`.
Guards use C-style truth values. Invalid random-assignment probabilities enable
no transition: the denominator must be nonzero and the rational ratio in `[0,1]`.
Bernoulli and uniform sampling are derived constructs, not additional primitives.

`Code.ofStmt` and `Code.append` implement right-associative sequencing. The
initial-fragment constructor adds a final `↓` continuation so even a standalone
call, query, or observation has the sequenced form required by the rules. Runtime
code should be built through these functions; a raw `Code.stmt (Stmt.seq ...)`
does not have an operational rule. `return` and `endquery` are runtime markers.
Stack lists have their top at the head; ordinary rules require nonempty stacks,
and only `term` and `err` remove the bottom marker.

`Step` and `Run` are indexed families in `Type`, preserving distinct derivations.
In particular, when both branches of a random assignment coincide, even with
equal probabilities, both contribute to `transitionWeight` and
`terminationProbability`. Labels are exact rationals; sums take values in
Mathlib's extended nonnegative reals. These are mass functions: bounds by one
and the subdistribution laws remain to be proved. Divergent runs contribute no
termination mass, and an always-rejected query keeps retrying.

`initialProgram` and `programSemantics` follow Section 4.2's ordinary call to
main. Section 3 instead describes sampling a query to main; `initialQuery`
provides that entry separately. The two entry conventions are not assumed equal.

The denotational definitions use the same ambient mass functions `α → ℝ≥0∞`
as the operational termination probabilities. `IsSubdistribution` and the
subtype `Subdistribution` express the bound on total mass. `LinOp` records
preservation of subdistributions and linearity in the paper's delta-expansion
formulation. The transformers are defined on ambient mass functions so their
construction does not require any closure proofs at this stage.

`whileFunctional` is the paper's Φ; `whileSemantics` is the pointwise supremum
of `Φ^k(0)`. `recursionFunctional` is the joint Ψ on pairs of function families
`(α, β)`; `recursiveEnvironment` is the pointwise supremum of `Ψ^k(0,0)`.
Finite iterates are available as `whileApproximation` and
`recursionApproximation`. The query component uses the old α and β in the
rejection equation, rather than normalizing intermediate approximations.
`normalize` separately defines the paper's 𝒩, including zero for an
almost-surely rejected query. Its denominator is `1 - q(error)`, which retains
divergence mass. The output domain is `Option (Value S)`, with `none` for error.

`ValidProbabilities` and `ValidProgramProbabilities` record the paper's domain
restriction on random assignments. On this domain the denotational clauses
follow the paper; outside it, a random assignment's invalid normal-store row
is extended to zero, matching the absence of operational transitions.
`Denotational.programSemantics` uses the ordinary-call entry and
`Denotational.queryProgramSemantics` uses the query entry.

No closure, linearity, continuity, fixed-point, normalization-equivalence, or
operational/denotational equivalence proofs have been added. In particular, the
Kleene suprema are definitions; their least-fixed-point properties remain to be
proved. The explicit pPDA translation and bounded-call syntax are also not included.
