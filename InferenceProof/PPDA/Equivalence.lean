module

public import InferenceProof.PPDA.Translation
public import InferenceProof.PPDA.OperationalWalk

set_option linter.style.header false

/-! # Equivalence of the program polynomial system and operational runs -/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {S : Signature} (E : ExprInterpretation S) (P : Program S) (C : Stmt S)

def rawConfiguration (c : ProgramControl P C) (stack : List (ProgramSymbol P C)) :
    InferenceProof.Configuration S := ⟨c.1.1, c.2, stack.map Subtype.val⟩

theorem rawControl_injective (U : Finset (Code S)) :
    Function.Injective (@rawControl S U) := by
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg (fun c : Control S => c.1) h))
    (congrArg (fun c : Control S => c.2) h)

theorem rawConfiguration_injective :
    Function.Injective (fun x : ProgramControl P C × List (ProgramSymbol P C) =>
      rawConfiguration P C x.1 x.2) := by
  intro a b h
  apply Prod.ext
  · exact rawControl_injective _ (Prod.ext (congrArg InferenceProof.Configuration.code h)
      (congrArg InferenceProof.Configuration.store h))
  · exact (List.map_injective_iff.mpr Subtype.val_injective)
      (congrArg InferenceProof.Configuration.stack h)

theorem Replacement.map_injective {α β : Type*} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Replacement.map f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Replacement.map, hf.eq_iff]

noncomputable def programEdgePartition (c : ProgramControl P C) (X : ProgramSymbol P C) :
    (Σ r, Σ w, ProgramEdge E P C c X r w) ≃ ProgramBranch E P C c X where
  toFun e := e.2.2.1
  invFun edge := ⟨branchTarget E P C edge, branchReplacement E P C edge, edge, rfl, rfl⟩
  left_inv e := by
    rcases e with ⟨r, w, edge, hr, hw⟩
    cases hr
    cases hw
    rfl
  right_inv _ := rfl

theorem ProgramEdge.raw_target {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    (edge : ProgramEdge E P C c X r w) : rawControl r = edge.1.move.target := by
  exact (congrArg rawControl edge.2.1).symm

theorem ProgramEdge.raw_replacement {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    (edge : ProgramEdge E P C c X r w) : w.map Subtype.val = edge.1.move.replacement := by
  exact (congrArg (Replacement.map Subtype.val) edge.2.2).symm.trans
    (raw_liftReplacement _ _ _)

/-- Transport an enabled head rule to its exact finite-state target and stack suffix. -/
noncomputable def ProgramEdge.witness {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    (edge : ProgramEdge E P C c X r w) (tail : List (ProgramSymbol P C))
    (hb : Boundary X.1 (tail.map Subtype.val)) :
    {step : Step E P (rawConfiguration P C c (X :: tail)) edge.1.move.probability
      (rawConfiguration P C r (w.word ++ tail)) // stepBranch step = edge.1.choice} := by
  let original := headMove_witness E P (rawControl c) X.1 edge.1.choice edge.1.move
    edge.1.enabled (tail.map Subtype.val) hb
  have htarget :
      (⟨edge.1.move.target.1, edge.1.move.target.2,
        edge.1.move.replacement.word ++ tail.map Subtype.val⟩ : InferenceProof.Configuration S) =
      rawConfiguration P C r (w.word ++ tail) := by
    rw [← edge.raw_target E P C, ← edge.raw_replacement E P C, Replacement.word_map]
    simp only [rawConfiguration, rawControl, List.map_append]
  let transported := castStep htarget original.1
  exact ⟨transported.1, transported.2.trans original.2⟩

noncomputable def programEdgeWeight {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    (edge : ProgramEdge E P C c X r w) : ℝ≥0∞ := ENNReal.ofReal (edge.1.move.probability : ℝ)

/-- Decode a branch-labelled pPDA path into the original operational semantics. -/
noncomputable def decodePath {c : ProgramControl P C} {stack : List (ProgramSymbol P C)}
    {q : ProgramControl P C} (path : BranchPath (ProgramEdge E P C) c stack q)
    (hg : Grounded (stack.map Subtype.val)) :
    OperationalWalk E P (rawConfiguration P C c stack) (rawConfiguration P C q []) := by
  induction path with
  | nil q => exact .nil _
  | pop edge rest ih =>
    let step := edge.witness E P C _ hg.boundary
    exact .cons ⟨_, step.1⟩ (ih (step_grounded step.1 hg))
  | one edge rest ih =>
    let step := edge.witness E P C _ hg.boundary
    exact .cons ⟨_, step.1⟩ (ih (step_grounded step.1 hg))
  | two edge rest ih =>
    let step := edge.witness E P C _ hg.boundary
    exact .cons ⟨_, step.1⟩ (ih (step_grounded step.1 hg))

/-- A uniform constructor for all three replacement lengths. -/
def BranchPath.prependStep {Q Γ : Type*} {Edge : Q → Γ → Q → Replacement Γ → Type*}
    {p : Q} {X : Γ} {r : Q} {w : Replacement Γ} {tail : List Γ} {q : Q}
    (edge : Edge p X r w) (rest : BranchPath Edge r (w.word ++ tail) q) :
    BranchPath Edge p (X :: tail) q :=
  match w with
  | .pop => .pop edge rest
  | .one _ => .one edge rest
  | .two _ _ => .two edge rest

theorem decode_prependStep {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    {tail : List (ProgramSymbol P C)} {q : ProgramControl P C}
    (edge : ProgramEdge E P C c X r w)
    (rest : BranchPath (ProgramEdge E P C) r (w.word ++ tail) q)
    (hg : Grounded ((X :: tail).map Subtype.val)) :
    decodePath E P C (BranchPath.prependStep edge rest) hg =
      .cons ⟨_, (edge.witness E P C tail hg.boundary).1⟩
        (decodePath E P C rest
          (step_grounded (edge.witness E P C tail hg.boundary).1 hg)) := by
  cases w <;> rfl

theorem decode_weight {c : ProgramControl P C} {stack : List (ProgramSymbol P C)}
    {q : ProgramControl P C} (path : BranchPath (ProgramEdge E P C) c stack q)
    (hg : Grounded (stack.map Subtype.val)) :
    (decodePath E P C path hg).weight = path.weight _ (programEdgeWeight E P C) := by
  induction path with
  | nil => rfl
  | pop edge rest ih =>
    change ENNReal.ofReal (edge.1.move.probability : ℝ) *
      (decodePath E P C rest _).weight = ENNReal.ofReal (edge.1.move.probability : ℝ) *
        rest.weight _ (programEdgeWeight E P C)
    exact congrArg (fun x => ENNReal.ofReal (edge.1.move.probability : ℝ) * x) (ih _)
  | one edge rest ih =>
    change ENNReal.ofReal (edge.1.move.probability : ℝ) *
      (decodePath E P C rest _).weight = ENNReal.ofReal (edge.1.move.probability : ℝ) *
        rest.weight _ (programEdgeWeight E P C)
    exact congrArg (fun x => ENNReal.ofReal (edge.1.move.probability : ℝ) * x) (ih _)
  | two edge rest ih =>
    change ENNReal.ofReal (edge.1.move.probability : ℝ) *
      (decodePath E P C rest _).weight = ENNReal.ofReal (edge.1.move.probability : ℝ) *
        rest.weight _ (programEdgeWeight E P C)
    exact congrArg (fun x => ENNReal.ofReal (edge.1.move.probability : ℝ) * x) (ih _)

def OperationalWalk.firstBranch {source target : InferenceProof.Configuration S} :
    OperationalWalk E P source target → Option Bool
  | .nil _ => none
  | .cons edge _ => some (stepBranch edge.2)

def OperationalWalk.tailView {source target : InferenceProof.Configuration S} :
    OperationalWalk E P source target →
      Option (Σ middle : InferenceProof.Configuration S, OperationalWalk E P middle target)
  | .nil _ => none
  | .cons _ rest => some ⟨_, rest⟩

theorem OperationalWalk.cons_right_injective
    {source middle target : InferenceProof.Configuration S}
    (edge : Σ p : ℚ, Step E P source p middle) :
    Function.Injective (fun rest : OperationalWalk E P middle target =>
      OperationalWalk.cons edge rest) := by
  intro a b h
  have ht := Option.some.inj (congrArg (OperationalWalk.tailView E P) h)
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using ht

theorem decode_firstBranch {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r : ProgramControl P C} {w : Replacement (ProgramSymbol P C)}
    {tail : List (ProgramSymbol P C)} {q : ProgramControl P C}
    (edge : ProgramEdge E P C c X r w)
    (rest : BranchPath (ProgramEdge E P C) r (w.word ++ tail) q)
    (hg : Grounded ((X :: tail).map Subtype.val)) :
    (decodePath E P C (BranchPath.prependStep edge rest) hg).firstBranch E P =
      some edge.1.choice := by
  rw [decode_prependStep]
  exact congrArg some (edge.witness E P C tail hg.boundary).2

theorem decode_root_eq {c : ProgramControl P C} {X : ProgramSymbol P C}
    {r₁ r₂ : ProgramControl P C} {w₁ w₂ : Replacement (ProgramSymbol P C)}
    {tail : List (ProgramSymbol P C)} {q : ProgramControl P C}
    (a : ProgramEdge E P C c X r₁ w₁) (b : ProgramEdge E P C c X r₂ w₂)
    (ra : BranchPath (ProgramEdge E P C) r₁ (w₁.word ++ tail) q)
    (rb : BranchPath (ProgramEdge E P C) r₂ (w₂.word ++ tail) q)
    (hg : Grounded ((X :: tail).map Subtype.val))
    (h : decodePath E P C (BranchPath.prependStep a ra) hg =
      decodePath E P C (BranchPath.prependStep b rb) hg) :
    (⟨r₁, w₁, a⟩ : Σ r, Σ w, ProgramEdge E P C c X r w) = ⟨r₂, w₂, b⟩ := by
  apply (programEdgePartition E P C c X).injective
  apply Branch.ext
  have ht := congrArg (OperationalWalk.firstBranch E P) h
  rw [decode_firstBranch, decode_firstBranch] at ht
  exact Option.some.inj ht

theorem decode_injective (c : ProgramControl P C) (stack : List (ProgramSymbol P C))
    (q : ProgramControl P C) (hg : Grounded (stack.map Subtype.val)) :
    Function.Injective (fun path : BranchPath (ProgramEdge E P C) c stack q =>
      decodePath E P C path hg) := by
  intro a
  induction a with
  | nil => intro b h; cases b; rfl
  | pop edge rest ih =>
    intro b h
    cases b with
    | pop other rb =>
      have hr := decode_root_eq E P C edge other rest rb hg h
      cases hr
      apply congrArg (BranchPath.pop edge)
      apply ih
      exact OperationalWalk.cons_right_injective E P _ h
    | one other rb => cases decode_root_eq E P C edge other rest rb hg h
    | two other rb => cases decode_root_eq E P C edge other rest rb hg h
  | one edge rest ih =>
    intro b h
    cases b with
    | pop other rb => cases decode_root_eq E P C edge other rest rb hg h
    | one other rb =>
      have hr := decode_root_eq E P C edge other rest rb hg h
      cases hr
      apply congrArg (BranchPath.one edge)
      apply ih
      exact OperationalWalk.cons_right_injective E P _ h
    | two other rb => cases decode_root_eq E P C edge other rest rb hg h
  | two edge rest ih =>
    intro b h
    cases b with
    | pop other rb => cases decode_root_eq E P C edge other rest rb hg h
    | one other rb => cases decode_root_eq E P C edge other rest rb hg h
    | two other rb =>
      have hr := decode_root_eq E P C edge other rest rb hg h
      cases hr
      apply congrArg (BranchPath.two edge)
      apply ih
      exact OperationalWalk.cons_right_injective E P _ h

theorem step_source_nonempty {source target : InferenceProof.Configuration S} {p : ℚ}
    (step : Step E P source p target) : source.stack ≠ [] := by
  cases step <;> exact List.cons_ne_nil _ _

theorem OperationalWalk.cons_heq {source target : InferenceProof.Configuration S}
    {a b : Σ middle : InferenceProof.Configuration S, Σ p : ℚ, Step E P source p middle}
    (h : a = b) (ra : OperationalWalk E P a.1 target) (rb : OperationalWalk E P b.1 target)
    (hr : HEq ra rb) : HEq (OperationalWalk.cons a.2 ra) (OperationalWalk.cons b.2 rb) := by
  cases h
  cases hr
  rfl

/-- Every operational terminating walk starting inside the finite model lifts
back to its exact sequence of head-rule instances. -/
theorem decode_surjective_aux {source target : InferenceProof.Configuration S}
    (walk : OperationalWalk E P source target) :
    ∀ (c : ProgramControl P C) (stack : List (ProgramSymbol P C)) (q : ProgramControl P C)
      (_hs : rawConfiguration P C c stack = source)
      (_ht : rawConfiguration P C q [] = target) (hg : Grounded (stack.map Subtype.val)),
      ∃ path : BranchPath (ProgramEdge E P C) c stack q,
        HEq (decodePath E P C path hg) walk := by
  induction walk with
  | nil source =>
    intro c stack q hs ht hg
    have h := @rawConfiguration_injective S P C (c, stack) (q, []) (hs.trans ht.symm)
    obtain ⟨hc, hstack⟩ := Prod.mk.inj h
    subst c
    subst stack
    cases ht
    exact ⟨.nil q, HEq.rfl⟩
  | @cons source middle target edge rest ih =>
    intro c stack q hs ht hg
    cases hs
    cases ht
    rcases edge with ⟨p, step⟩
    cases stack with
    | nil => exact False.elim (step_source_nonempty E P step rfl)
    | cons X tail =>
      obtain ⟨m, hm, _, _, _⟩ := headMove_complete E P (codeSet P C) (rawControl c) X.1
        (tail.map Subtype.val) (codeSet_closed P C _ c.1.2) step
      let branch : ProgramBranch E P C c X := ⟨stepBranch step, m, hm⟩
      let r := branchTarget E P C branch
      let w := branchReplacement E P C branch
      let edge : ProgramEdge E P C c X r w := ⟨branch, rfl, rfl⟩
      let chosen := edge.witness E P C tail hg.boundary
      have heq :
          (⟨m.probability, rawConfiguration P C r (w.word ++ tail), chosen.1⟩ :
            FullEdge E P (rawConfiguration P C c (X :: tail))) = ⟨p, middle, step⟩ :=
        fullEdge_ext E P (codeSet P C) (rawControl c) X.1 (tail.map Subtype.val)
          (codeSet_closed P C _ c.1.2) _ _ chosen.2
      have hsource := congrArg (fun z : FullEdge E P (rawConfiguration P C c (X :: tail)) =>
        z.2.1) heq
      obtain ⟨path, hpath⟩ := ih r (w.word ++ tail) q hsource rfl (step_grounded chosen.1 hg)
      refine ⟨BranchPath.prependStep edge path, ?_⟩
      rw [decode_prependStep]
      have hroot := congrArg
        (fun z : FullEdge E P (rawConfiguration P C c (X :: tail)) =>
          (⟨z.2.1, z.1, z.2.2⟩ : Σ middle : InferenceProof.Configuration S,
            Σ p : ℚ, Step E P (rawConfiguration P C c (X :: tail)) p middle)) heq
      exact OperationalWalk.cons_heq E P hroot _ _ hpath

theorem decode_surjective (c : ProgramControl P C) (stack : List (ProgramSymbol P C))
    (q : ProgramControl P C) (hg : Grounded (stack.map Subtype.val)) :
    Function.Surjective (fun path : BranchPath (ProgramEdge E P C) c stack q =>
      decodePath E P C path hg) := by
  intro walk
  obtain ⟨path, hpath⟩ := decode_surjective_aux E P C walk c stack q rfl rfl hg
  exact ⟨path, eq_of_heq hpath⟩

noncomputable def programPathEquiv (c : ProgramControl P C)
    (stack : List (ProgramSymbol P C)) (q : ProgramControl P C)
    (hg : Grounded (stack.map Subtype.val)) :
    BranchPath (ProgramEdge E P C) c stack q ≃
      OperationalWalk E P (rawConfiguration P C c stack) (rawConfiguration P C q []) :=
  Equiv.ofBijective (fun path => decodePath E P C path hg)
    ⟨decode_injective E P C c stack q hg, decode_surjective E P C c stack q hg⟩

/-- The rational transition sum and the rule-instance mass sum are identical. -/
theorem programWeight_eq_aggregated :
    programWeight E P C = aggregatedWeight (ProgramEdge E P C) (programEdgeWeight E P C) := by
  funext c X r w
  unfold programWeight programTransition aggregatedWeight programEdgeWeight
  rw [tsum_fintype]
  have hcast : ((∑ edge : ProgramEdge E P C c X r w, edge.1.move.probability : ℚ) : ℝ) =
      ∑ edge : ProgramEdge E P C c X r w, (edge.1.move.probability : ℝ) :=
    map_sum (Rat.castHom ℝ) _ _
  rw [hcast]
  exact ENNReal.ofReal_sum_of_nonneg fun edge _ =>
    Rat.cast_nonneg.mpr edge.1.probability_nonnegative

theorem program_leastSolution_eq_branchPaths (c : ProgramControl P C)
    (X : ProgramSymbol P C) (q : ProgramControl P C) :
    leastSolution (programWeight E P C) c X q =
      ∑' path : BranchPath (ProgramEdge E P C) c [X] q,
        path.weight _ (programEdgeWeight E P C) := by
  rw [programWeight_eq_aggregated, leastSolution_eq_sum_path,
    sum_branchPath_eq_sum_path]

/-- The finite head-variable polynomial system computes exactly the operational
termination probability, for every source fragment and every initial/final store.
No finiteness, simulation, or path-aggregation assumptions are supplied by callers.
-/
theorem polynomialTermination_eq_operational (σ₀ σ : Valuation S) :
    polynomialTermination E P C σ₀ σ =
      InferenceProof.terminationProbability E P (initialFragment C σ₀) σ := by
  unfold polynomialTermination
  rw [program_leastSolution_eq_branchPaths, operational_termination_eq_sum_walk]
  let c : ProgramControl P C :=
    (⟨compile C .done, locations_subset_codeSet P C (compile_mem_locations C .done)⟩, σ₀)
  let X : ProgramSymbol P C := ⟨.bottom, trivial⟩
  let q : ProgramControl P C := (⟨.done, done_mem_codeSet P C⟩, σ)
  have hg : Grounded ([X].map Subtype.val) := Grounded.bottom
  change (∑' path : BranchPath (ProgramEdge E P C) c [X] q,
      path.weight _ (programEdgeWeight E P C)) =
    ∑' walk : OperationalWalk E P (rawConfiguration P C c [X])
      (rawConfiguration P C q []), walk.weight
  rw [← (programPathEquiv E P C c [X] q hg).tsum_eq]
  exact tsum_congr fun path => (decode_weight E P C path hg).symm

end InferenceProof.PPDA
