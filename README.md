# inference-proof

Lean 4 formalization of *Exact Inference for Nested Discrete Probabilistic
Programs*, with sources in `../paper`. Build with `lake build`; import
`InferenceProof` to use the formalization.

The development proves denotational well-definedness, the loop and simultaneous
recursion least-fixed-point results, recursive query normalization, and equality
of denotational semantics, operational termination probabilities, and the finite
pPDA polynomial termination system. There are no proof placeholders or custom
axioms.

| Module | Contents |
| --- | --- |
| `Syntax` | Finite variable, function, and value domains; expressions; statements; function definitions and programs |
| `SemanticsCommon` | Stores, callee initialization `init_i`, expression evaluation, and rational branch probabilities |
| `OperationalSemantics` | Runtime code, stack frames, small-step rules, finite runs, and termination probabilities |
| `DenotationalSemantics` | Distribution transformers, marginals, guard restrictions, normalization, and Phi/Psi iterates |
| [`Denotational`](InferenceProof/Denotational/README.md) | Closure, linearity, continuity, least fixed points, and query normalization (Section 5 and its appendix) |
| [`PPDA`](InferenceProof/PPDA/README.md) | Finite automata, the quadratic termination system, and equivalence with operational runs (Sections 2 and 4) |
| [`Equivalence`](InferenceProof/Equivalence/README.md) | Operational/denotational equivalence, composition laws, and bounded-loop suprema (Section 6 and its appendix) |

Calls implicitly pass the callee's designated parameter variables. `Store.init`
preserves their values and sets every other callee variable to zero;
`FunctionDef.init` also preserves the error valuation. The call rule saves the
caller store. On return, only the target variable is updated in that saved store.
The denotational function kernel uses the same initialization before evaluating
the body and taking its output marginal.

Random assignment has two weighted transitions when its evaluated outcomes are
distinct, and one probability-one transition when they are equal (`rndAssignEq`).
Probability expressions must have nonzero denominator and rational ratio in
`[0,1]`. Invalid normal-store rows have no operational transitions and zero
denotational mass; `ValidProbabilities` and `ValidProgramProbabilities` express
the paper's validity domain.

`Signature` supplies the unspecified unary and binary operator symbols;
`ExprInterpretation` supplies their total interpretations on `Fin (M + 1)`.
Guards use C-style truth values. `Code.ofStmt` and `Code.append` normalize
sequencing and supply the final `↓` continuation needed by calls, queries, and
observations. Stack lists have their top at the head; the bottom marker is
removed only on termination. The final `return out` is supplied by the call rule.

Distributions are nonnegative mass functions into `ℝ≥0∞`. Total mass is proved
at most one for semantic kernels; missing mass represents divergence. Error
mass is retained separately, and query rejection retries from the saved caller
store. Query normalization divides successful output mass by `1 - q(error)`,
retaining divergence; certain rejection yields zero.

The ordinary-call entry in Section 4.2 is `initialProgram` and
`Denotational.programSemantics`. The query entry described in Section 3 is
`initialQuery` and `Denotational.queryProgramSemantics`. Both have equivalence
theorems; they are not identified with each other.
