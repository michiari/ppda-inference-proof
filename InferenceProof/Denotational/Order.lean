module

public import InferenceProof.Denotational.Mass

set_option linter.style.header false

/-! # The domain-theoretic infrastructure of Appendix A

We use Mathlib's omega-complete partial orders and Scott continuity on chains.
Subdistributions inherit their order and increasing suprema from mass functions.
Function spaces and products then have the pointwise omega-cpo structures of
Lemma `lem:comp-cpo`.
-/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {α β γ ι : Type*}

/-- Mathlib's Scott continuity on increasing chains, expressed using only the
underlying orders. This is definitionally `ωScottContinuous`; spelling out its
body avoids competing omega-supremum instances on complete function lattices.
-/
abbrev ChainContinuous [PartialOrder α] [PartialOrder β] (f : α → β) : Prop :=
  ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f

namespace ChainContinuous

variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
  [OmegaCompletePartialOrder γ]

theorem monotone {f : α → β} (h : ChainContinuous f) : Monotone f :=
  ωScottContinuous.monotone h

theorem comp {f : α → β} {g : β → γ}
    (hg : ChainContinuous g) (hf : ChainContinuous f) : ChainContinuous (g ∘ f) :=
  ωScottContinuous.comp hg hf

theorem id : ChainContinuous (id : α → α) := ωScottContinuous.id

theorem const {b : β} : ChainContinuous (fun _ : α => b) := ωScottContinuous.const

omit [OmegaCompletePartialOrder α] in
theorem apply (a : α) : ChainContinuous (fun f : α → β => f a) :=
  ωScottContinuous.apply a

omit [OmegaCompletePartialOrder β] in
theorem apply₂ {f : α → β → γ} (hf : ChainContinuous f) (b : β) :
    ChainContinuous (fun a => f a b) := ωScottContinuous.apply₂ hf b

omit [OmegaCompletePartialOrder β] in
theorem of_apply₂ {f : α → β → γ} (hf : ∀ b, ChainContinuous (fun a => f a b)) :
    ChainContinuous f := ωScottContinuous.of_apply₂ hf

theorem prodMk {f : α → β} {g : α → γ} (hf : ChainContinuous f)
    (hg : ChainContinuous g) : ChainContinuous (fun a => (f a, g a)) :=
  Prod.ωScottContinuous.prodMk hf hg

theorem fst : ChainContinuous (Prod.fst : α × β → α) := Prod.ωScottContinuous_fst

theorem snd : ChainContinuous (Prod.snd : α × β → β) := Prod.ωScottContinuous_snd

end ChainContinuous

theorem ChainContinuous.iSup [OmegaCompletePartialOrder α] [CompleteLattice β]
    {f : ι → α → β} (hf : ∀ i, ChainContinuous (f i)) : ChainContinuous (⨆ i, f i) :=
  CompleteLattice.ωScottContinuous.iSup hf

theorem omegaContinuous_of_monotone_iSup [CompleteLattice α] [CompleteLattice β]
    {f : α → β} (hf : Monotone f)
    (hs : ∀ c : ℕ → α, Monotone c → f (⨆ n, c n) = ⨆ n, f (c n)) :
    ChainContinuous f :=
  ωScottContinuous.of_monotone_map_ωSup ⟨hf, fun c => hs c c.monotone⟩

theorem omegaContinuous_iSup [CompleteLattice α] [CompleteLattice β]
    {f : α → β} (hf : ChainContinuous f) (c : ℕ → α) (hc : Monotone c) :
    f (⨆ n, c n) = ⨆ n, f (c n) :=
  ωScottContinuous.map_ωSup hf ⟨⟨c, hc⟩⟩

theorem omegaContinuous_add [CompleteLattice α] {f g : α → ℝ≥0∞}
    (hf : ChainContinuous f) (hg : ChainContinuous g) :
    ChainContinuous (fun a => f a + g a) := by
  apply omegaContinuous_of_monotone_iSup
    (fun _ _ h => add_le_add (hf.monotone h) (hg.monotone h))
  intro c hc
  rw [omegaContinuous_iSup hf c hc, omegaContinuous_iSup hg c hc]
  exact ENNReal.iSup_add_iSup_of_monotone (hf.monotone.comp hc) (hg.monotone.comp hc)

theorem omegaContinuous_mul [CompleteLattice α] {f g : α → ℝ≥0∞}
    (hf : ChainContinuous f) (hg : ChainContinuous g) :
    ChainContinuous (fun a => f a * g a) := by
  apply omegaContinuous_of_monotone_iSup
    (fun _ _ h => mul_le_mul' (hf.monotone h) (hg.monotone h))
  intro c hc
  rw [omegaContinuous_iSup hf c hc, omegaContinuous_iSup hg c hc]
  exact iSup_mul_of_monotone (hf.monotone.comp hc) (hg.monotone.comp hc)

theorem omegaContinuous_tsum [CompleteLattice α] {f : α → ι → ℝ≥0∞}
    (hf : ∀ i, ChainContinuous (fun a => f a i)) :
    ChainContinuous (fun a => ∑' i, f a i) := by
  apply omegaContinuous_of_monotone_iSup
    (fun _ _ h => ENNReal.tsum_le_tsum (fun i => (hf i).monotone h))
  intro c hc
  simp_rw [omegaContinuous_iSup (hf _) c hc]
  exact tsum_iSup_of_monotone _ fun _ _ h i => (hf i).monotone (hc h)

theorem omegaContinuous_bind [CompleteLattice α]
    {p : α → Mass β} {K : α → β → Mass γ}
    (hp : ChainContinuous p) (hK : ChainContinuous K) :
    ChainContinuous (fun a => bind (p a) (K a)) := by
  apply omegaContinuous_of_monotone_iSup
    (fun _ _ h => bind_mono (hp.monotone h) (hK.monotone h))
  intro c hc
  rw [omegaContinuous_iSup hp c hc, omegaContinuous_iSup hK c hc]
  exact bind_iSup _ _ (hp.monotone.comp hc) (hK.monotone.comp hc)

instance : PartialOrder (Subdistribution α) :=
  inferInstanceAs (PartialOrder {p : Mass α // IsSubdistribution p})

instance : OrderBot (Subdistribution α) where
  bot := ⟨0, isSubdistribution_zero⟩
  bot_le p := show (0 : Mass α) ≤ p.1 from fun _ => bot_le

instance : OmegaCompletePartialOrder (Subdistribution α) where
  ωSup c := ⟨⨆ n, (c n).1, isSubdistribution_iSup _
    (fun _ _ h => c.monotone h) (fun n => (c n).2)⟩
  le_ωSup c n := show (c n).1 ≤ ⨆ k, (c k).1 from le_iSup (fun k => (c k).1) n
  ωSup_le c p h := show (⨆ n, (c n).1) ≤ p.1 from iSup_le h

/-- The pointwise supremum remains a subdistribution. -/
theorem subdistribution_omegaSup (c : Chain (Subdistribution α)) :
    (ωSup c).1 = ⨆ n, (c n).1 := rfl

/-- Suprema of increasing sequences, without requiring arbitrary suprema. -/
def chainSup {L : Type*} [OmegaCompletePartialOrder L] (a : ℕ → L) (ha : Monotone a) : L :=
  ωSup ⟨⟨a, ha⟩⟩

theorem le_chainSup {L : Type*} [OmegaCompletePartialOrder L]
    (a : ℕ → L) (ha : Monotone a) (n : ℕ) : a n ≤ chainSup a ha :=
  le_ωSup ⟨⟨a, ha⟩⟩ n

theorem chainSup_le {L : Type*} [OmegaCompletePartialOrder L]
    (a : ℕ → L) (ha : Monotone a) {x : L} (h : ∀ n, a n ≤ x) : chainSup a ha ≤ x :=
  ωSup_le ⟨⟨a, ha⟩⟩ x h

theorem chainSup_monotone {L : Type*} [OmegaCompletePartialOrder L]
    (a : ℕ → ℕ → L) (h₁ : ∀ j, Monotone (fun i => a i j)) (h₂ : ∀ i, Monotone (a i)) :
    Monotone (fun i => chainSup (a i) (h₂ i)) := by
  intro i j hij
  exact chainSup_le _ _ (fun k => (h₁ k hij).trans (le_chainSup _ _ k))

/-- Appendix A, Lemma `lem:double-index`, on an arbitrary omega-cpo. -/
theorem chainSup_diagonal {L : Type*} [OmegaCompletePartialOrder L]
    (a : ℕ → ℕ → L) (h₁ : ∀ j, Monotone (fun i => a i j)) (h₂ : ∀ i, Monotone (a i)) :
    chainSup (fun i => chainSup (a i) (h₂ i)) (chainSup_monotone a h₁ h₂) =
      chainSup (fun n => a n n) (fun _ _ h => (h₁ _ h).trans (h₂ _ h)) := by
  apply le_antisymm
  · apply chainSup_le
    intro i
    apply chainSup_le
    intro j
    exact ((h₁ j (Nat.le_max_left i j)).trans (h₂ _ (Nat.le_max_right i j))).trans
      (le_chainSup (fun n => a n n) (fun _ _ h => (h₁ _ h).trans (h₂ _ h)) (max i j))
  · apply chainSup_le
    intro n
    exact (le_chainSup (a n) (h₂ n) n).trans
      (le_chainSup (fun i => chainSup (a i) (h₂ i)) (chainSup_monotone a h₁ h₂) n)

theorem chainSup_comm {L : Type*} [OmegaCompletePartialOrder L]
    (a : ℕ → ℕ → L) (h₁ : ∀ j, Monotone (fun i => a i j)) (h₂ : ∀ i, Monotone (a i)) :
    chainSup (fun i => chainSup (a i) (h₂ i)) (chainSup_monotone a h₁ h₂) =
      chainSup (fun j => chainSup (fun i => a i j) (h₁ j))
        (chainSup_monotone (fun j i => a i j) h₂ h₁) := by
  rw [chainSup_diagonal a h₁ h₂, chainSup_diagonal (fun j i => a i j) h₂ h₁]

/-- Section 5, Theorem `thm:kleene`, on an arbitrary omega-cpo with bottom.
`IsLUB` expresses the displayed supremum without assuming a complete lattice.
-/
theorem kleene_theorem {L : Type*} [OmegaCompletePartialOrder L] [OrderBot L]
    (f : L → L) (hf : ChainContinuous f) :
    ∃ a, IsLeast (Function.fixedPoints f) a ∧
      IsLUB (Set.range (fun n : ℕ => f^[n] ⊥)) a := by
  let F : L →𝒄 L := ContinuousHom.ofFun f hf
  refine ⟨ωSup (fixedPoints.iterateChain F.toOrderHom ⊥ bot_le), ?_, ?_⟩
  · exact ⟨fixedPoints.ωSup_iterate_mem_fixedPoint F ⊥ bot_le,
      fun a ha => fixedPoints.ωSup_iterate_le_fixedPoint F ⊥ bot_le ha bot_le⟩
  · exact isLUB_range_ωSup (fixedPoints.iterateChain F.toOrderHom ⊥ bot_le)

/-- Kleene's theorem in the ambient complete lattice, with a pre-fixed-point
leastness statement. Subdistribution membership is established separately.
-/
theorem kleene_fixedPoint [CompleteLattice α] (f : α → α) (hf : ChainContinuous f) :
    f (⨆ n, f^[n] ⊥) = ⨆ n, f^[n] ⊥ := by
  rw [omegaContinuous_iSup hf _ (hf.monotone.monotone_iterate_of_le_map bot_le)]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup_of_le (n + 1)
      (Function.iterate_succ_apply' f n ⊥).ge
  · refine iSup_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n => exact le_iSup_of_le n (Function.iterate_succ_apply' f n ⊥).le

theorem kleene_le [CompleteLattice α] {f : α → α} (hf : Monotone f) {a : α}
    (ha : f a ≤ a) : (⨆ n, f^[n] ⊥) ≤ a := by
  apply iSup_le
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hf ih).trans ha

end

end InferenceProof.Denotational
