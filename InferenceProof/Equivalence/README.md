# Operational and denotational equivalence

This directory proves Section 6, Theorem `thm:equivalence`, and the theorem
in `Appendix: Proof of Section \ref{sec:equivalence}`. Import
`InferenceProof.Equivalence` or `InferenceProof`. Declarations are in
`InferenceProof.Equivalence` unless qualified otherwise below.

The main theorem is:

```lean
denotational_eq_operational (E : ExprInterpretation S) (P : Program S)
    (C : Stmt S) (σ : Valuation S) :
  Denotational.fragmentSemantics E P C σ = InferenceProof.fragmentSemantics E P C σ
```

Both sides are the original semantic definitions. In particular, the right
side is the sum over the original rationally labelled `Run` derivations.
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
| Main and appendix equivalence theorem | `denotational_eq_operational` in `Main.lean` |
| Skip, observation, assignment, and probabilistic assignment | `sourceWP_skip`, `sourceWP_observe`, `sourceWP_assign`, `sourceWP_randomAssign`; matching `runtime_*` equations; structural cases of `auxiliarySemantics_le_runtime` |
| Distinct random branches with coincident stores | Existing `Step`/`Run` multiplicities and `Branch` choices are preserved by `branchEdgeEquiv`; `sum_branches` sums them |
| Sequencing and delta expansion | `expect_bind`, `sourceWP_seq`, `codeWP_compile`, and the sequencing case of `auxiliarySemantics_le_runtime`; `operational_seq` exposes the resulting kernel equation |
| Conditional, including error input | `sourceWP_ite`, `runtime_ite`, `operational_ite`, and `operational_error` |
| Finite loop unfoldings | `expect_whileApproximation_succ`, `expect_whileApproximation_error`, and the finite-iterate induction in `auxiliarySemantics_le_runtime` |
| Source `diverge` and bounded while syntax | `diverge`, `boundedWhile`, `semantics_diverge`, `semantics_boundedWhile_iterate`, `boundedWhile_equivalence` in `BoundedLoops.lean` |
| Supremum of bounded loops | `semantics_while_eq_iSup_boundedWhile`, `operational_while_eq_iSup_boundedWhile`, and `operational_while_eq_iSup` |
| Equations `eq:sem-k-func-asgmt`, `eq:sem-k-sq-asgmt` | Existing `functionAssign`/`sampleQueryAssign`, interpreted at `recursionApproximation E P k`; `sourceWP_call` and `sourceWP_sampleQuery` give their weighted sums |
| Equations `eq:alphak`, `eq:betak` and induction on k | `sourceWP_call_succ`, `sourceWP_sampleQuery_succ`, `recursionApproximation_callsBelow` |
| Call/return diagram and equation `eq:op-func` | `runtime_call`, `runtime_return`, `runtimeDenotation_return`, `runtimeDenotation_call`, and `operational_call` |
| Query/rejection diagram | `runtime_sampleQuery`, `runtime_endQuery`, `runtime_error_query`, `runtimeDenotation_query`, and `operational_sampleQuery` |
| Increasing supremum over call/query bounds | `sourceWP_recursiveEnvironment`, `semantics_le_runtime`, and `operational_eq_iSup_recursionApproximation` (specialize to calls or queries) |
| All terminating runs have finite length | `boundedRunSum`, `terminationProbability_eq_iSup`, `terminationProbability_fixedPoint` |
| Runtime equations compute the original operational semantics | `runtime_iterate_eq_bounded`, `runtimeValue_eq_terminationProbability` |
| Every operational run contributes to the denotation | `configurationDenotation_prefixed`, `runtimeValue_le_denotation` |
| Operational query normalization | `functionSemantics_eq_marginal_operational`, `operational_sampleQuery_eq_normalize` |

The runtime comparison uses the already verified `PPDA.headMove` evaluator.
`branchEdgeEquiv` identifies its enabled Boolean choices with actual operational
rule instances. The existing finite-code/stack invariant `PPDA.InProgram` is
proved for initial fragments and preserved by every operational step. Induction
on run-length cutoffs therefore identifies the runtime Kleene supremum with
the original operational run sum. This bridge retains zero-weight branches
and aggregates coincident outcomes correctly.

The reverse comparison is proved structurally for every finite recursive
environment. The call case enters the function body at the preceding bound;
the query case uses the preceding alpha and beta, exactly as in `eq:betak`.
Continuity in the environment removes the bound. The forward comparison uses
the loop and recursion fixed-point equations to interpret saved frames as a
pre-fixed point of the runtime operator. Leastness then accounts for every
finite operational run.

## Representation differences and corrections

- The formalization carries call/query bounds in the environment instead of
  adding bounded call constructors to `Stmt` and a second bounded pPDA. The
  paper's informal run-inclusion diagrams are replaced by the two proved
  comparisons above. This avoids assuming the diagrams' compositionality
  claims, and proves the same unbounded equivalence theorem. Literal bounded
  call syntax is not needed by this proof.
- The appendix identifies the zero source unrolling (`diverge`) with the zero
  operator. This fails on error input: every source statement propagates the
  error valuation. In Lean, `semantics_diverge` proves the exact transformer
  `errorPart`, and source unrollings are `Phi^[n] errorPart`. They lie between
  `Phi^[n] 0` and `Phi^[n+1] 0`, so their supremum is the same least fixed point.
  `BoundedLoops.lean` proves both the corrected identity and the supremum result.
  A nonzero constant is supplied for `true` in these syntactic-sugar theorems;
  the main equivalence theorem needs no such assumption.
- Random-assignment probabilities are valid in the paper's language. The
  existing Lean definitions additionally make invalid normal-store rows zero,
  with no operational transitions. Equivalence covers this common extension,
  so it needs no additional validity assumptions. Error input still propagates.
- The paper's piecewise random-assignment explanation must sum both branches
  when their updates coincide. Both original semantics do so, and the proof
  preserves this behavior. No distinct-outcome hypothesis is introduced.

No original syntax or semantic definition body was changed. There are no
placeholders or custom axioms.

## Files

`Expectation` and `SourceEquations` establish the mass algebra and source
equations. `Operational` and `Runtime` connect actual runs to head equations.
`RuntimeEquations` gives each operational continuation law. `Continuations`
and `Soundness` prove the operational-to-denotational comparison. `LoopApproximants`,
`Structural`, and `Recursion` prove the opposite comparison. `Main` combines
them. `Constructs` and `BoundedLoops` expose the paper-facing corollaries.
