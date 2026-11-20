module

public import InferenceProof.Denotational.Auxiliary

set_option linter.style.header false

/-! # Continuity in the recursive environment

Appendix A, Lemma `lem:psem-cont`, by structural induction. Sequencing uses
the diagonal-supremum argument of `lem:double-index`. For loops, continuity
is first established for each finite Phi iterate and then for their supremum.
-/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {α β γ : Type*} {S : Signature}

/-- Joint continuity of evaluation when each function being evaluated is continuous. -/
theorem omegaContinuous_application [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]
    {F : α → β → γ} {g : α → β} (hF : ChainContinuous F) (hg : ChainContinuous g)
    (hrow : ∀ a, ChainContinuous (F a)) : ChainContinuous (fun a => F a (g a)) := by
  apply omegaContinuous_of_monotone_iSup
  · intro a b hab
    exact (hF.monotone hab (g a)).trans ((hrow b).monotone (hg.monotone hab))
  · intro c hc
    rw [omegaContinuous_iSup hF c hc, omegaContinuous_iSup hg c hc, iSup_apply]
    simp_rw [omegaContinuous_iSup (hrow _) (fun n => g (c n)) (hg.monotone.comp hc)]
    exact iSup_diagonal _ (fun _ _ _ h => hF.monotone (hc h) _)
      (fun i _ _ h => (hrow (c i)).monotone (hg.monotone (hc h)))

theorem functionAssign_omegaContinuous (x : Var S) :
    ChainContinuous (functionAssign x) := by
  apply ChainContinuous.of_apply₂
  intro p
  unfold ChainContinuous
  apply omegaContinuous_bind ChainContinuous.const
  unfold ChainContinuous
  apply ChainContinuous.of_apply₂
  intro σ
  cases σ with
  | error => exact ChainContinuous.const
  | normal σ =>
    unfold ChainContinuous
    exact omegaContinuous_bind (ChainContinuous.apply (Valuation.normal σ)) ChainContinuous.const

theorem sampleQueryAssign_omegaContinuous (x : Var S) :
    ChainContinuous (sampleQueryAssign x) := by
  apply ChainContinuous.of_apply₂
  intro p
  unfold ChainContinuous
  apply omegaContinuous_bind ChainContinuous.const
  unfold ChainContinuous
  apply ChainContinuous.of_apply₂
  intro σ
  cases σ with
  | error => exact ChainContinuous.const
  | normal σ =>
    apply ChainContinuous.of_apply₂
    intro σ'
    apply omegaContinuous_tsum
    intro v
    exact omegaContinuous_mul ((ChainContinuous.apply (Valuation.normal σ)).apply₂ (some v))
      ChainContinuous.const

theorem marginal_omegaContinuous (x : Var S) : ChainContinuous (marginal x) := by
  unfold ChainContinuous
  exact omegaContinuous_bind ChainContinuous.id ChainContinuous.const

theorem functionFromBody_omegaContinuous (F : FunctionDef S) :
    ChainContinuous (functionFromBody F) := by
  apply ChainContinuous.of_apply₂
  intro σ
  exact (marginal_omegaContinuous F.out).comp (ChainContinuous.apply (dirac (F.init σ)))

theorem whileApproximation_omegaContinuous [CompleteLattice α]
    (E : ExprInterpretation S) (b : Expr S) {body : α → Transformer S}
    (hbody : ChainContinuous body) (lbody : ∀ a, MassLinear (body a)) (n : ℕ) :
    ChainContinuous (fun a => whileApproximation E b (body a) n) := by
  induction n with
  | zero => exact ChainContinuous.const
  | succ n ih =>
    simp only [whileApproximation, Function.iterate_succ_apply']
    apply ChainContinuous.of_apply₂
    intro p
    apply ChainContinuous.of_apply₂
    intro σ
    apply omegaContinuous_add
    · apply omegaContinuous_add ChainContinuous.const
      exact (omegaContinuous_application ih (hbody.apply₂ (restrict E b true p))
        (fun a => (whileApproximation_massLinear E b (lbody a) n).omegaContinuous)).apply₂ σ
    · exact ChainContinuous.const

theorem whileSemantics_omegaContinuous [CompleteLattice α]
    (E : ExprInterpretation S) (b : Expr S) {body : α → Transformer S}
    (hbody : ChainContinuous body) (lbody : ∀ a, MassLinear (body a)) :
    ChainContinuous (fun a => whileSemantics E b (body a)) := by
  have h := ChainContinuous.iSup
    (fun n => whileApproximation_omegaContinuous E b hbody lbody n)
  have heq : (⨆ n, fun a => whileApproximation E b (body a) n) =
      (fun a => whileSemantics E b (body a)) := by
    funext a p σ
    simp only [whileSemantics, iSup_apply]
  rw [heq] at h
  simpa only [ChainContinuous] using h

/-- Appendix A, Lemma `lem:psem-cont`, on the ambient matrix space.
In particular it holds on the paper's subprobability-kernel domain.
-/
theorem auxiliarySemantics_omegaContinuous (E : ExprInterpretation S) (C : Stmt S) :
    ChainContinuous (fun env : Environment S => auxiliarySemantics E env C) := by
  induction C with
  | assign | randomAssign | skip | observe => exact ChainContinuous.const
  | call x f =>
    exact (functionAssign_omegaContinuous x).comp (ChainContinuous.fst.apply₂ f)
  | sampleQuery x f =>
    exact (sampleQueryAssign_omegaContinuous x).comp (ChainContinuous.snd.apply₂ f)
  | seq a c iha ihc =>
    change ChainContinuous (fun env p => auxiliarySemantics E env c
      (auxiliarySemantics E env a p))
    apply ChainContinuous.of_apply₂
    intro p
    exact omegaContinuous_application ihc (iha.apply₂ p)
      (fun env => (auxiliarySemantics_massLinear E env c).omegaContinuous)
  | ite b t e iht ihe =>
    apply ChainContinuous.of_apply₂
    intro p
    apply ChainContinuous.of_apply₂
    intro σ
    exact omegaContinuous_add (omegaContinuous_add
      ((iht.apply₂ (restrict E b true p)).apply₂ σ)
      ((ihe.apply₂ (restrict E b false p)).apply₂ σ)) ChainContinuous.const
  | «while» b body ih =>
    exact whileSemantics_omegaContinuous E b ih
      (fun env => auxiliarySemantics_massLinear E env body)

theorem auxiliarySemantics_monotone (E : ExprInterpretation S) (C : Stmt S) :
    Monotone (fun env : Environment S => auxiliarySemantics E env C) :=
  (auxiliarySemantics_omegaContinuous E C).monotone

theorem auxiliarySemantics_iSup (E : ExprInterpretation S) (C : Stmt S)
    (env : ℕ → Environment S) (h : Monotone env) :
    auxiliarySemantics E (⨆ n, env n) C = ⨆ n, auxiliarySemantics E (env n) C :=
  omegaContinuous_iSup (auxiliarySemantics_omegaContinuous E C) env h

end

end InferenceProof.Denotational
