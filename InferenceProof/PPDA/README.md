# pPDA termination probabilities

The program-specific equivalence is proved. Import `InferenceProof.PPDA` (or
`InferenceProof`) to use the results. All declarations below are in
`InferenceProof.PPDA`.

For every expression interpretation `E`, program `P`, source fragment `C`, and
initial/final valuations `σ₀ σ`, the main theorems are:

```lean
polynomialTermination_eq_operational E P C σ₀ σ :
  polynomialTermination E P C σ₀ σ =
    InferenceProof.terminationProbability E P (initialFragment C σ₀) σ

ppdaTermination_eq_operational E P C σ₀ σ :
  ppdaTermination E P C σ₀ σ =
    InferenceProof.terminationProbability E P (initialFragment C σ₀) σ
```

`polynomialTermination` uses the least solution of the finite head-variable
polynomial system. `ppdaTermination` uses the least solution for the normalized
finite rational automaton `programAutomaton E P C`. The two are equal by
`ppdaTermination_eq_polynomial`. `ppdaTermination_eq_programSemantics` specializes
the result to the whole-program entry convention of Section 4.2.

These theorems require no additional finiteness, simulation, normalization, or
path-aggregation hypotheses. There are no proof placeholders or custom axioms.

The mathematical sources are `paper/2-background.tex`, subsection "Termination
Probabilities", and the program semantics of `paper/4-operational.tex`, Section
4.2. The first-return argument follows `bibliography/esparza/lmcs2004.tex`, Theorem
`thm-least-fix` and the preceding decomposition of paths after pushing two symbols.

The generic polynomial and path-sum development consists of:

- `Basic.lean`: finite rational pPDAs, with nonnegative normalized transitions.
- `Polynomial.lean`: the finite quadratic operator on variables `[p X | q]`,
  monotonicity, its least solution, the fixed-point equations, and leastness.
- `Kleene.lean`: preservation of increasing suprema and equality of the least
  solution with the supremum of polynomial iterates from zero.
- `Paths.lean`: a weight-preserving bijection between terminating pushdown paths
  and forests of first-return derivations. Binary derivations retain the
  intermediate control state.
- `TreeSum.lean`: bounded-height tree sums equal polynomial iterates;
  `Automaton.terminationProbability_eq_sum_path` identifies the least polynomial
  solution with the sum of all terminating pPDA path weights.

All three program-specific tasks previously listed here are now completed:

1. `CodeClosure.lean` constructs a finite, continuation-closed set of runtime
   locations directly from the source and function bodies. `FiniteModel.lean`
   derives finite control and stack-symbol types from these locations and the
   finite store domain. `Reachability.lean` defines Section 4.2's exact
   positive-probability reachable sets and proves `reachableControls_finite` and
   `reachableSymbols_finite` by containment in the constructed finite carriers.
2. `HeadMachine.lean` extracts the local transition table. `headMove_witness`
   realizes every enabled head rule above an admissible suffix, while
   `headMove_complete` recovers every operational step at a compiled location.
   `Grounded` and `step_grounded` enforce the stack boundary convention: bottom
   is the final symbol and is popped only when alone; function/query returns and
   error unwinding retain a nonempty suffix. `headMove_closed` proves that local
   transitions stay in the finite carriers.
3. `StepIdentity.lean` proves that the Boolean rule choice identifies an exact
   operational rule instance. `Translation.lean` constructs rational coefficients
   by summing enabled instances with the same target and replacement word.
   `Branching.lean` proves that aggregating such instances preserves path mass.
   `OperationalPaths.lean` and `OperationalWalk.lean` reindex the original `Run`
   sum without losing accumulated labels or branch multiplicity.
   `Equivalence.lean` constructs the weight-preserving `programPathEquiv` and
   proves `polynomialTermination_eq_operational`. Both random-assignment branches
   contribute separately even when their probabilities and successors coincide.

There are two deliberate representation choices relative to the paper:

- The automaton uses a finite syntactic superset of the reachable controls and
  symbols. This avoids making reachability decidability part of the construction
  and includes all final stores, even unreachable ones. The exact reachable sets
  are separately defined and proved finite; the unconditional path equivalence
  proves that the extra locations do not change termination from the initial
  configuration.
- Some control/head combinations in this superset have no operational rule.
  Invalid random-assignment probabilities also enable no rule in the existing
  semantics. `Normalization.lean` proves that every row has mass zero or one and
  completes zero rows with a deterministic self-loop. `Completion.lean` proves
  that this completion leaves the least polynomial solution unchanged, so the
  constructed `programAutomaton` satisfies the background definition's row-sum
  requirement without imposing new program-validity assumptions.

The polynomial operator lives in the complete lattice of nonnegative
extended-real vectors, with exact rational coefficients and finite sums.
Equivalence with the operational mass function is proved. Empty-stack absorbing
self-loops are omitted from finite paths so each terminating first-hit path is
counted once. The [equivalence development](../Equivalence/README.md) additionally
proves operational/denotational equivalence, equality with this polynomial
system, and the bound on total termination mass by one.
