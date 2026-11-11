module

public import InferenceProof.Denotational.Primitives

set_option linter.style.header false

/-! # Existence and well-definedness of the while fixed point

This is Appendix A's `lem:lfp-while-lemma`: Phi maps LinOp to LinOp,
preserves increasing suprema, and its iterates from zero have a least fixed
point. The body assumption is precisely membership in the paper's LinOp.
-/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature} (E : ExprInterpretation S) (b : Expr S)

theorem preserves_comp {T U : Transformer S} (hU : PreservesSubdistributions U)
    (hT : PreservesSubdistributions T) : PreservesSubdistributions (U ∘ T) :=
  fun p hp => hU (T p) (hT p hp)

theorem branching_isLinear {T U : Transformer S} (hT : IsLinear T) (hU : IsLinear U) :
    IsLinear (fun p => T (restrict E b true p) + U (restrict E b false p) + errorPart p) :=
  ((hT.comp (restrict_massLinear E b true).isLinear (restrict_preserves E b true)).add
    (hU.comp (restrict_massLinear E b false).isLinear (restrict_preserves E b false))).add
      errorPart_massLinear.isLinear

theorem branching_preserves {T U : Transformer S}
    (hT : PreservesSubdistributions T) (lT : IsLinear T)
    (hU : PreservesSubdistributions U) (lU : IsLinear U) :
    PreservesSubdistributions
      (fun p => T (restrict E b true p) + U (restrict E b false p) + errorPart p) := by
  intro p hp
  calc
    _ = totalMass (T (restrict E b true p)) + totalMass (U (restrict E b false p)) +
        totalMass (errorPart p) := by rw [totalMass_add, totalMass_add]
    _ ≤ totalMass (restrict E b true p) + totalMass (restrict E b false p) +
        totalMass (errorPart p) := add_le_add
          (add_le_add (lT.totalMass_le hT (restrict_preserves E b true p hp))
            (lU.totalMass_le hU (restrict_preserves E b false p hp))) le_rfl
    _ = totalMass p := by
      rw [add_comm (totalMass (restrict E b true p)), ← totalMass_add, ← totalMass_add,
        restrict_partition]
    _ ≤ 1 := hp

theorem whileFunctional_monotone (body : Transformer S) :
    Monotone (whileFunctional E b body) := by
  intro T U h p σ
  exact add_le_add (add_le_add le_rfl (h _ σ)) le_rfl

theorem whileFunctional_iSup (body : Transformer S) (T : ℕ → Transformer S) :
    whileFunctional E b body (⨆ n, T n) = ⨆ n, whileFunctional E b body (T n) := by
  funext p σ
  simp only [whileFunctional, Pi.add_apply, iSup_apply, ENNReal.add_iSup, ENNReal.iSup_add]

theorem whileFunctional_omegaContinuous (body : Transformer S) :
    ChainContinuous (whileFunctional E b body) :=
  omegaContinuous_of_monotone_iSup (whileFunctional_monotone E b body)
    (fun T _ => whileFunctional_iSup E b body T)

theorem whileApproximation_monotone (body : Transformer S) :
    Monotone (whileApproximation E b body) :=
  (whileFunctional_monotone E b body).monotone_iterate_of_le_map bot_le

theorem whileSemantics_fixedPoint (body : Transformer S) :
    whileFunctional E b body (whileSemantics E b body) = whileSemantics E b body :=
  kleene_fixedPoint _ (whileFunctional_omegaContinuous E b body)

theorem whileSemantics_le (body : Transformer S) {T : Transformer S}
    (h : whileFunctional E b body T ≤ T) : whileSemantics E b body ≤ T :=
  kleene_le (whileFunctional_monotone E b body) h

theorem whileFunctional_isLinear {body T : Transformer S}
    (hbody : PreservesSubdistributions body) (lbody : IsLinear body) (lT : IsLinear T) :
    IsLinear (whileFunctional E b body T) :=
  (((restrict_massLinear E b false).isLinear).add
    ((lT.comp lbody hbody).comp (restrict_massLinear E b true).isLinear
      (restrict_preserves E b true))).add errorPart_massLinear.isLinear

theorem whileFunctional_preserves {body T : Transformer S}
    (hbody : PreservesSubdistributions body) (lbody : IsLinear body)
    (hT : PreservesSubdistributions T) (lT : IsLinear T) :
    PreservesSubdistributions (whileFunctional E b body T) := by
  have h := branching_preserves E b (preserves_comp hT hbody)
    (lT.comp lbody hbody) (fun _ hp => hp) massLinear_id.isLinear
  intro p hp
  simpa only [whileFunctional, Function.comp_apply, id_eq, add_comm, add_left_comm,
    add_assoc] using h p hp

theorem whileApproximation_linOp {body : Transformer S}
    (hbody : PreservesSubdistributions body) (lbody : IsLinear body) (n : ℕ) :
    PreservesSubdistributions (whileApproximation E b body n) ∧
      IsLinear (whileApproximation E b body n) := by
  induction n with
  | zero => exact ⟨fun _ _ => isSubdistribution_zero, massLinear_zero.isLinear⟩
  | succ n ih =>
    rw [whileApproximation, Function.iterate_succ_apply']
    exact ⟨whileFunctional_preserves E b hbody lbody ih.1 ih.2,
      whileFunctional_isLinear E b hbody lbody ih.2⟩

/-- The semantic supremum lies in LinOp, not merely in the ambient mass space. -/
theorem whileSemantics_linOp {body : Transformer S}
    (hbody : PreservesSubdistributions body) (lbody : IsLinear body) :
    PreservesSubdistributions (whileSemantics E b body) ∧ IsLinear (whileSemantics E b body) :=
  ⟨preservesSubdistributions_iSup _
    (fun n => (whileApproximation_linOp E b hbody lbody n).1)
    (whileApproximation_monotone E b body),
    isLinear_iSup _ (fun n => (whileApproximation_linOp E b hbody lbody n).2)
      (whileApproximation_monotone E b body)⟩

theorem whileFunctional_massLinear {body T : Transformer S}
    (hbody : MassLinear body) (hT : MassLinear T) :
    MassLinear (whileFunctional E b body T) :=
  ((restrict_massLinear E b false).add
    ((hT.comp hbody).comp (restrict_massLinear E b true))).add errorPart_massLinear

theorem whileApproximation_massLinear {body : Transformer S} (hbody : MassLinear body) (n : ℕ) :
    MassLinear (whileApproximation E b body n) := by
  induction n with
  | zero => exact massLinear_zero
  | succ n ih =>
    rw [whileApproximation, Function.iterate_succ_apply']
    exact whileFunctional_massLinear E b hbody ih

theorem whileSemantics_massLinear {body : Transformer S} (hbody : MassLinear body) :
    MassLinear (whileSemantics E b body) :=
  massLinear_iSup _ (whileApproximation_massLinear E b hbody)
    (whileApproximation_monotone E b body)

/-- Phi as a map on exactly the paper's space of linear subdistribution transformers. -/
def whileOperator (body : LinOp S) (T : LinOp S) : LinOp S :=
  ⟨whileFunctional E b body.1 T.1,
    whileFunctional_preserves E b body.2.1 body.2.2 T.2.1 T.2.2,
    whileFunctional_isLinear E b body.2.1 body.2.2 T.2.2⟩

def whileFixedPoint (body : LinOp S) : LinOp S :=
  ⟨whileSemantics E b body.1, whileSemantics_linOp E b body.2.1 body.2.2⟩

theorem whileOperator_omegaContinuous (body : LinOp S) :
    ChainContinuous (whileOperator E b body) := by
  apply ωScottContinuous.of_monotone_map_ωSup
  refine ⟨fun T U h => whileFunctional_monotone E b body.1 h, ?_⟩
  intro c
  apply Subtype.ext
  change whileFunctional E b body.1 (⨆ n, (c n).1) =
    ⨆ n, whileFunctional E b body.1 (c n).1
  exact whileFunctional_iSup E b body.1 _

/-- Leastness with the paper's order: candidates need only be pre-fixed on
subdistribution inputs, irrespective of their ambient extension.
-/
theorem whileSemantics_le_on_subdistributions {body T : Transformer S}
    (hbody : PreservesSubdistributions body)
    (hT : ∀ p, IsSubdistribution p → whileFunctional E b body T p ≤ T p)
    (p : StoreMass S) (hp : IsSubdistribution p) : whileSemantics E b body p ≤ T p := by
  have hiter (n : ℕ) :
      ∀ q, IsSubdistribution q → whileApproximation E b body n q ≤ T q := by
    induction n with
    | zero => exact fun _ _ => bot_le
    | succ n ih =>
      intro q hq
      rw [whileApproximation, Function.iterate_succ_apply']
      intro σ
      exact (add_le_add (add_le_add le_rfl
        (ih _ (hbody _ (restrict_preserves E b true q hq)) σ)) le_rfl).trans (hT q hq σ)
  change (⨆ n, whileApproximation E b body n) p ≤ T p
  rw [iSup_apply]
  exact iSup_le fun n => hiter n p hp

/-- Appendix A, Lemma `lem:lfp-while-lemma`, including leastness in LinOp. -/
theorem whileFixedPoint_isLeast (body : LinOp S) :
    IsLeast (Function.fixedPoints (whileOperator E b body)) (whileFixedPoint E b body) := by
  refine ⟨Subtype.ext (whileSemantics_fixedPoint E b body.1), ?_⟩
  intro T hT
  exact whileSemantics_le E b body.1
    (congrArg Subtype.val (show whileOperator E b body T = T from hT)).le

end

end InferenceProof.Denotational
