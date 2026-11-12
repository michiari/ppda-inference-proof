# Well-definedness of the denotational semantics

This directory proves the results in `paper/5-denotational.tex` and the first
section of `paper/appendix.tex`, ending before the operational/denotational
equivalence appendix. Import `InferenceProof.Denotational` or `InferenceProof`.
The original semantic definitions remain in `DenotationalSemantics.lean`.
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
point. The final query-normalization proof uses the appendix's pre-fixed pair
`(alpha-star, normalize alpha-star)` and leastness of Psi.

| Paper result | Lean declaration or instance |
| --- | --- |
| Delta expansion of a distribution | `bind_dirac_right` in `Mass.lean` |
| Appendix `lem:comp-cpo` | Mathlib's function and product omega-cpo instances; subdistribution, LinOp, and subprobability-environment instances in `Order.lean`, `Linear.lean`, and `Auxiliary.lean` |
| Appendix `lem:op-seq` | `ENNReal.iSup_add_iSup_of_monotone`, `iSup_mul_of_monotone`, and `tsum_iSup_of_monotone` |
| Appendix `lem:double-index` | `chainSup_diagonal` and `chainSup_comm`, on an arbitrary omega-cpo; `iSup_diagonal` is the complete-lattice form used in semantic continuity |
| Section 5 `thm:kleene` | `kleene_theorem`, on an arbitrary omega-cpo with bottom; `kleene_fixedPoint` and `kleene_le` give the ambient-lattice form |
| Appendix `lem:lfp-while-lemma` | `whileFunctional_preserves`, `whileFunctional_isLinear`, `whileOperator_omegaContinuous`, `whileSemantics_linOp`, and `whileFixedPoint_isLeast` in `While.lean` |
| Appendix `lem:sem-linear` | `auxiliarySemantics_massLinear`, `auxiliarySemantics_linOp`, and `semantics_linOp` |
| Section 5 `thm:fixed-point-while` | `semantics_while_isLeast`, with `whileSemantics_fixedPoint` and the definition `whileSemantics` |
| Section 5 / Appendix `lem:psem-cont` | `auxiliarySemantics_omegaContinuous` and `auxiliarySemantics_iSup` in `Continuity.lean` |
| Section 5 `thm:fixed-point-rec` | `recursionFunctional_preserves`, `recursionOperator_omegaContinuous`, `recursiveEnvironment_subprobability`, `recursiveEnvironment_fixedPoint`, and `recursionFixedPoint_isLeast` in `FixedPoints.lean` |
| Section 5 `eq:N-fix-point` | `normalize_fixedPoint`, `rejection_fixedPoint_unique`, and `normalize_isLeast` in `Rejection.lean` |
| Section 5 / Appendix `prop:sq-normalization` | `sampleQuerySemantics_eq_normalize` in `QueryNormalization.lean` |

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
10. `QueryNormalization.lean`: the appendix's recursive normalization argument.

Representation details relative to the paper:

- The existing definitions use ambient functions into nonnegative extended reals.
  Membership in the paper's domains is proved, rather than assumed:
  `IsSubdistribution`, `LinOp`, and `SubprobabilityEnvironment` carry the bounds.
  `fragmentSemantics_isSubdistribution`, `programSemantics_isSubdistribution`,
  `functionSemantics_isSubdistribution`, and
  `sampleQuerySemantics_isSubdistribution` expose these bounds to callers.
- `MassLinear` is delta expansion on every ambient mass function, a stronger
  property proved for constructed statement transformers. `IsLinear` remains
  the original paper-facing property on subdistribution inputs. The existing
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
- The original semantics extends invalid random-assignment rows by zero.
  The closure and fixed-point proofs cover that extension too, so they need
  no extra validity hypotheses. On the paper's probability-validity domain
  they apply directly to the stated semantics.

There are no placeholders or custom axioms. No semantic definition was changed
for these proofs. Operational/denotational equivalence is proved in the
[separate equivalence development](../Equivalence/README.md).
