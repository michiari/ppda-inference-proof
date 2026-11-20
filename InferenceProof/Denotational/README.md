# Well-definedness of the denotational semantics

This directory proves the well-definedness results in Sections 5 and 13 of
the paper (Denotational Semantics and its appendix). Import
`InferenceProof.Denotational` or `InferenceProof`.
The semantic definitions are in `DenotationalSemantics.lean`.
All declarations below are in `InferenceProof.Denotational`.

The main results are:

- `semantics_linOp E P C`: every statement preserves subdistributions and is
  linear in the paper's delta-expansion sense.
- `whileSemantics_fixedPoint` and `whileSemantics_le`: the defined supremum of
  Phi iterates is a fixed point and is below every pre-fixed transformer.
  `whileSemantics_linOp` proves membership in LinOp when the body is in LinOp.
- `recursiveEnvironment_fixedPoint`, `recursiveEnvironment_le`, and
  `recursiveEnvironment_subprobability`: the defined supremum of Psi iterates
  is its least fixed point, and every function and query row is a subdistribution.
- `sampleQuerySemantics_eq_normalize E P f σ`: the recursive query kernel is
  exactly the normalization of the recursive function kernel, including zero
  for certain rejection.

The proofs follow the paper's arguments: increasing suprema commute with
nonnegative sums and products; the semantic domains are omega-cpos; linearity
and environment continuity follow by structural induction; loops use finite
Phi iterates; and Kleene iteration constructs the simultaneous recursion fixed
point. The final query-normalization proof uses the pre-fixed pair in Section 13.1
`(alpha-star, normalize alpha-star)` and leastness of Psi.

| Paper result | Lean declaration or instance |
| --- | --- |
| Section 5.1: delta expansion of a distribution | `bind_dirac_right` in `Mass.lean` |
| Lemma 13.1 | Mathlib's function and product omega-cpo instances; subdistribution, LinOp, and subprobability-environment instances in `Order.lean`, `Linear.lean`, and `Auxiliary.lean` |
| Lemma 13.2 | `ENNReal.iSup_add_iSup_of_monotone`, `iSup_mul_of_monotone`, and `tsum_iSup_of_monotone` |
| Lemma 13.3 | `chainSup_diagonal` and `chainSup_comm`, on an arbitrary omega-cpo; `iSup_diagonal` is the complete-lattice form used in semantic continuity |
| Theorem 5.2 (Kleene’s fixed-point theorem) | `kleene_theorem`, on an arbitrary omega-cpo with bottom; `kleene_fixedPoint` and `kleene_le` give the ambient-lattice form |
| Lemma 13.4 | `whileFunctional_preserves`, `whileFunctional_isLinear`, `whileOperator_omegaContinuous`, `whileSemantics_linOp`, and `whileFixedPoint_isLeast` in `While.lean` |
| Lemma 13.5 | `auxiliarySemantics_massLinear`, `auxiliarySemantics_linOp`, and `semantics_linOp` |
| Theorems 5.3 and 13.6 (loop fixed point) | `semantics_while_isLeast`, with `whileSemantics_fixedPoint` and the definition `whileSemantics` |
| Lemma 5.5 (Section 5.2; proof in Section 13.1) | `auxiliarySemantics_omegaContinuous` and `auxiliarySemantics_iSup` in `Continuity.lean` |
| Theorem 5.4 (simultaneous recursion fixed point) | `recursionFunctional_preserves`, `recursionOperator_omegaContinuous`, `recursiveEnvironment_subprobability`, `recursiveEnvironment_fixedPoint`, and `recursionFixedPoint_isLeast` in `FixedPoints.lean` |
| Equation (6), Section 5.1 (rejection fixed point) | `normalize_fixedPoint`, `rejection_fixedPoint_unique`, and `normalize_isLeast` in `Rejection.lean` |
| Proposition 5.6 (Section 5.2; proof in Section 13.1) | `sampleQuerySemantics_eq_normalize` in `QueryNormalization.lean` |

The files are arranged by dependency:

1. `Mass.lean`: kernel algebra, total mass, contraction, and increasing limits.
2. `Order.lean`: chain continuity, subdistribution omega-cpos, the diagonal
   argument, and Kleene's theorem.
3. `Linear.lean`: linear-transformer algebra and the LinOp omega-cpo.
4. `Primitives.lean`: assignment, observation, restriction, and call/query closure.
5. `While.lean`: Phi's closure, continuity, iterates, and least fixed point.
6. `Auxiliary.lean`: structural linearity and closure, matrix-domain omega-cpos,
   rejection closure, and preservation of the error store.
7. `Continuity.lean`: structural continuity in the recursive environment,
   using diagonal suprema for sequencing and finite loop iterates.
8. `FixedPoints.lean`: Psi and the well-defined full semantics.
9. `Rejection.lean`: normalization as the least affine rejection solution.
10. `QueryNormalization.lean`: the proof of Proposition 5.6 in Section 13.1.

Function kernels evaluate bodies on `dirac (F.init σ)`, implementing the
embedding `φ_i`. Callee initialization retains the values of parameter variables,
zeros other variables, and preserves error. `functionFromBody_omegaContinuous`
and `recursionFunctional_preserves` include this initialization.

Representation details relative to the paper:

- The existing definitions use ambient functions into nonnegative extended reals.
  Membership in the paper's domains is proved, rather than assumed:
  `IsSubdistribution`, `LinOp`, and `SubprobabilityEnvironment` carry the bounds.
  `fragmentSemantics_isSubdistribution`, `programSemantics_isSubdistribution`,
  `functionSemantics_isSubdistribution`, and
  `sampleQuerySemantics_isSubdistribution` expose these bounds to callers.
- `MassLinear` is delta expansion on every ambient mass function, a stronger
  property proved for constructed statement transformers. `IsLinear` remains
  the paper-facing property on subdistribution inputs. The
  LinOp representation retains an ambient extension; in addition to ambient
  leastness, `whileSemantics_le_on_subdistributions` proves leastness against
  candidates whose pre-fixed inequality is required only on the paper's domain.
- `ChainContinuous` abbreviates Mathlib's Scott-continuity-on-chains predicate.
  It is definitionally the body of `OmegaCompletePartialOrder.ωScottContinuous`;
  the spelling avoids competing omega-supremum instances for function lattices.
  It imposes no additional mathematical condition.
- The sum and product limit rules use extended nonnegative reals so unbounded
  increasing sequences also have suprema. All semantic probability rows are
  proved to have total mass at most one. Affine uniqueness is asserted for
  subdistribution solutions, as in the paper, since infinite-valued ambient
  solutions need not be unique.
- The semantics extends invalid random-assignment rows by zero.
  The closure and fixed-point proofs cover that extension too, so they need
  no extra validity hypotheses. On the paper's probability-validity domain
  they apply directly to the stated semantics.

There are no placeholders or custom axioms. Operational/denotational equivalence
is proved in the [equivalence development](../Equivalence/README.md).
