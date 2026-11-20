# Operational and denotational equivalence

This directory proves Theorem 6.1 in Section 6 and its restatement,
Theorem 14.1, in Section 14. Import
`InferenceProof.Equivalence` or `InferenceProof`. Declarations are in
`InferenceProof.Equivalence` unless qualified otherwise below.

The main theorem is:

```lean
denotational_eq_operational (E : ExprInterpretation S) (P : Program S)
    (C : Stmt S) (σ : Valuation S) :
  Denotational.fragmentSemantics E P C σ = InferenceProof.fragmentSemantics E P C σ
```

The right side is the sum over rationally labelled `Run` derivations.
The result includes every source construct, mutual recursion, nested queries,
nontermination, and the error valuation. No simulation, compositionality,
termination bound, or fixed-point equation is assumed by the theorem.

`denotational_eq_polynomial` also identifies the denotation with the existing
finite pPDA polynomial termination system. `programSemantics_eq_operational`
and `queryProgramSemantics_eq_operational` cover the two program entry
conventions separately. `operational_isSubdistribution` proves that the total
operational termination mass of a fragment is at most one.

## Proof and correspondence with the paper

The central induction follows the paper's source constructors, its finite Phi
iterates for loops, and its simultaneous alpha/beta iterates for recursion.
Continuation rewards record what happens after a fragment terminates. Thus
the induction applies to function bodies before `return` and to queries before
`endquery`, with the caller's saved store and outer stack kept explicit.
Rewards are arbitrary nonnegative extended-real functions; no extra boundedness
assumption is needed.

| Paper argument | Lean results |
| --- | --- |
| Theorems 6.1 and 14.1 | `denotational_eq_operational` in `Main.lean` |
| Section 14: skip, observation, assignment, and probabilistic assignment | `sourceWP_skip`, `sourceWP_observe`, `sourceWP_assign`, `sourceWP_randomAssign`; matching `runtime_*` equations; structural cases of `auxiliarySemantics_le_runtime` |
| Section 14 and Figure 4: random assignment, including equal outcomes | `Step.rndAssignLeft` and `Step.rndAssignRight` require distinct values; `Step.rndAssignEq` has probability one; `sourceWP_randomAssign_eq` proves the matching denotational identity |
| Section 14: sequencing and delta expansion | `expect_bind`, `sourceWP_seq`, `codeWP_compile`, and the sequencing case of `auxiliarySemantics_le_runtime`; `operational_seq` exposes the resulting kernel equation |
| Section 14: conditional, including error input | `sourceWP_ite`, `runtime_ite`, `operational_ite`, and `operational_error` |
| Section 14: finite loop unfoldings | `expect_whileApproximation_succ`, `expect_whileApproximation_error`, and the finite-iterate induction in `auxiliarySemantics_le_runtime` |
| Section 14: source `diverge` and bounded while syntax | `diverge`, `boundedWhile`, `semantics_diverge`, `semantics_boundedWhile_iterate`, `boundedWhile_equivalence` in `BoundedLoops.lean` |
| Section 14: supremum of bounded loops | `semantics_while_eq_iSup_boundedWhile`, `operational_while_eq_iSup_boundedWhile`, and `operational_while_eq_iSup` |
| Equations (11) and (12), Section 6 | Existing `functionAssign`/`sampleQueryAssign`, interpreted at `recursionApproximation E P k`; `sourceWP_call` and `sourceWP_sampleQuery` give their weighted sums |
| Equations (13) and (14), Section 6: induction on k | `sourceWP_call_succ`, `sourceWP_sampleQuery_succ`, `recursionApproximation_callsBelow` |
| Section 6, Figure 8 and Equation (16): call initialization and return | `runtime_call`, `runtime_return`, `runtimeDenotation_return`, `runtimeDenotation_call`, and `operational_call` |
| Section 6, Figure 9: query/rejection diagram | `runtime_sampleQuery`, `runtime_endQuery`, `runtime_error_query`, `runtimeDenotation_query`, and `operational_sampleQuery` |
| Section 6: increasing supremum over call/query bounds | `sourceWP_recursiveEnvironment`, `semantics_le_runtime`, and `operational_eq_iSup_recursionApproximation` (specialize to calls or queries) |
| All terminating runs have finite length | `boundedRunSum`, `terminationProbability_eq_iSup`, `terminationProbability_fixedPoint` |
| Runtime equations compute operational termination probabilities | `runtime_iterate_eq_bounded`, `runtimeValue_eq_terminationProbability` |
| Every operational run contributes to the denotation | `configurationDenotation_prefixed`, `runtimeValue_le_denotation` |
| Operational query normalization | `functionSemantics_eq_marginal_operational`, `operational_sampleQuery_eq_normalize` |

The runtime comparison uses the already verified `PPDA.headMove` evaluator.
`branchEdgeEquiv` identifies its enabled Boolean choices with actual operational
rule instances. The finite-code/stack invariant `PPDA.InProgram` is
proved for initial fragments and preserved by every operational step. Induction
on run-length cutoffs therefore identifies the runtime Kleene supremum with
the operational run sum, including zero-weight transitions.

The reverse comparison is proved structurally for every finite recursive
environment. The call case initializes the callee store and enters the body at the preceding bound;
the query case uses the preceding alpha and beta, exactly as in Equation (14).
Continuity in the environment removes the bound. The forward comparison uses
the loop and recursion fixed-point equations to interpret saved frames as a
pre-fixed point of the runtime operator. Leastness then accounts for every
finite operational run.

## Representation

Call/query bounds are carried in the environment. The structural induction
works for every continuation and grounded stack; the runtime first-step equations
and leastness justify the call and query diagrams.

`FunctionDef.init` is shared by the operational call rule and the denotational
embedding `φ_i`. It preserves parameter values and zeros all other variables;
returns restore the caller's saved store. Equal random outcomes take a single
probability-one operational transition, consistent with their combined mass in
the denotational formula.

As in Section 14, `semantics_diverge` gives `errorPart`, bounded source loops
are `Phi^[n] errorPart`, and comparison with successive zero-seed iterates proves
their supremum is the loop denotation. A nonzero constant supplies `true` in
these syntactic-sugar theorems; the main theorem needs no such assumption.

Invalid random-assignment rows are extended by zero on both sides. On the
paper's validity domain the theorems apply directly to its semantic clauses.
There are no placeholders or custom axioms.

## Files

`Expectation` and `SourceEquations` establish the mass algebra and source
equations. `Operational` and `Runtime` connect actual runs to head equations.
`RuntimeEquations` gives each operational continuation law. `Continuations`
and `Soundness` prove the operational-to-denotational comparison. `LoopApproximants`,
`Structural`, and `Recursion` prove the opposite comparison. `Main` combines
them. `Constructs` and `BoundedLoops` expose the paper-facing corollaries.
