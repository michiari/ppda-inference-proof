module

public import InferenceProof.Denotational.Order

set_option linter.style.header false

/-! # Kernel representations and linear transformers -/

@[expose] public section

open scoped ENNReal
open OmegaCompletePartialOrder

namespace InferenceProof.Denotational

noncomputable section

variable {α β γ : Type*} {S : Signature}

/-- Delta expansion on all ambient mass functions. This stronger property is
convenient for the constructed semantics; `IsLinear` only quantifies over
subdistributions, as in the paper.
-/
def MassLinear (T : Mass α → Mass β) : Prop :=
  ∀ p, T p = bind p (fun a => T (dirac a))

theorem massLinear_bind (K : α → Mass β) : MassLinear (fun p => bind p K) := by
  intro p
  simp only [bind_dirac]

theorem MassLinear.isLinear {T : Transformer S} (h : MassLinear T) : IsLinear T :=
  fun p _ => h p

theorem MassLinear.monotone {T : Mass α → Mass β} (h : MassLinear T) : Monotone T := by
  intro p q hp
  rw [h p, h q]
  exact bind_mono hp le_rfl

theorem MassLinear.omegaContinuous {T : Mass α → Mass β} (h : MassLinear T) :
    ChainContinuous T := by
  apply omegaContinuous_of_monotone_iSup h.monotone
  intro p hp
  rw [h (⨆ n, p n)]
  calc
    _ = ⨆ n, bind (p n) (fun a => T (dirac a)) := by
      simpa only [iSup_const] using bind_iSup p (fun _ => fun a => T (dirac a)) hp
        (fun _ _ _ => le_rfl)
    _ = _ := congrArg iSup (funext fun n => (h (p n)).symm)

theorem MassLinear.comp {T : Mass α → Mass β} {U : Mass β → Mass γ}
    (hU : MassLinear U) (hT : MassLinear T) : MassLinear (U ∘ T) := by
  intro p
  change U (T p) = bind p (fun a => U (T (dirac a)))
  rw [hU, hT p, bind_assoc]
  exact congrArg (bind p) (funext fun a => (hU (T (dirac a))).symm)

theorem MassLinear.add {T U : Mass α → Mass β} (hT : MassLinear T) (hU : MassLinear U) :
    MassLinear (fun p => T p + U p) := by
  intro p
  change T p + U p = bind p (fun a => T (dirac a) + U (dirac a))
  rw [hT p, hU p, bind_add_right]

theorem massLinear_id : MassLinear (id : Mass α → Mass α) :=
  fun _ => bind_dirac_right _ |>.symm

theorem massLinear_zero : MassLinear (fun _ : Mass α => (0 : Mass β)) :=
  fun _ => (bind_zero_right _).symm

theorem massLinear_iSup (T : ℕ → Mass α → Mass β) (hT : ∀ n, MassLinear (T n))
    (hmono : Monotone T) : MassLinear (⨆ n, T n) := by
  intro p
  funext b
  simp only [iSup_apply, bind]
  calc
    _ = ⨆ n, ∑' a, p a * T n (dirac a) b :=
      congrArg iSup (funext fun n => congrFun (hT n p) b)
    _ = _ := by
      rw [← tsum_iSup_of_monotone (fun n a => p a * T n (dirac a) b) (fun i j h a =>
        mul_le_mul' le_rfl (hmono h (dirac a) b))]
      simp only [ENNReal.mul_iSup]

theorem IsLinear.zero {T : Transformer S} (h : IsLinear T) : T 0 = 0 := by
  rw [h 0 isSubdistribution_zero]
  exact bind_zero _

theorem IsLinear.totalMass_le {T : Transformer S} (h : IsLinear T)
    (hT : PreservesSubdistributions T) {p : StoreMass S} (hp : IsSubdistribution p) :
    totalMass (T p) ≤ totalMass p := by
  rw [h p hp]
  exact totalMass_bind_le p _ (fun a => hT _ (isSubdistribution_dirac a))

theorem IsLinear.add {T U : Transformer S} (hT : IsLinear T) (hU : IsLinear U) :
    IsLinear (fun p => T p + U p) := by
  intro p hp
  change T p + U p = bind p (fun a => T (dirac a) + U (dirac a))
  rw [hT p hp, hU p hp, bind_add_right]
  rfl

theorem IsLinear.comp {T U : Transformer S} (hU : IsLinear U) (hT : IsLinear T)
    (hpres : PreservesSubdistributions T) : IsLinear (U ∘ T) := by
  intro p hp
  change U (T p) = bind p (fun a => U (T (dirac a)))
  rw [hU (T p) (hpres p hp), hT p hp]
  change bind (bind p (fun a => T (dirac a))) (fun b => U (dirac b)) = _
  rw [bind_assoc]
  exact congrArg (bind p) (funext fun a =>
    (hU (T (dirac a)) (hpres _ (isSubdistribution_dirac a))).symm)

theorem isLinear_iSup (T : ℕ → Transformer S) (hT : ∀ n, IsLinear (T n))
    (hmono : Monotone T) : IsLinear (⨆ n, T n) := by
  intro p hp
  funext b
  simp only [iSup_apply]
  calc
    _ = ⨆ n, ∑' a, p a * T n (dirac a) b :=
      congrArg iSup (funext fun n => congrFun (hT n p hp) b)
    _ = _ := by
      rw [← tsum_iSup_of_monotone (fun n a => p a * T n (dirac a) b) (fun i j h a =>
        mul_le_mul' le_rfl (hmono h (dirac a) b))]
      simp only [ENNReal.mul_iSup]

theorem preservesSubdistributions_iSup (T : ℕ → Transformer S)
    (hT : ∀ n, PreservesSubdistributions (T n)) (hmono : Monotone T) :
    PreservesSubdistributions (⨆ n, T n) := by
  intro p hp
  simpa only [iSup_apply] using
    isSubdistribution_iSup (fun n => T n p) (fun _ _ h => hmono h p)
      (fun n => hT n p hp)

instance : PartialOrder (LinOp S) :=
  inferInstanceAs (PartialOrder {T : Transformer S //
    PreservesSubdistributions T ∧ IsLinear T})

instance : OrderBot (LinOp S) where
  bot := ⟨fun _ => 0, (fun _ _ => isSubdistribution_zero), massLinear_zero.isLinear⟩
  bot_le T := show (fun _ => (0 : StoreMass S)) ≤ T.1 from fun _ _ => bot_le

/-- The linear-transformer omega-cpo used in the proof of `lem:lfp-while-lemma`. -/
instance : OmegaCompletePartialOrder (LinOp S) where
  ωSup c := ⟨⨆ n, (c n).1,
    preservesSubdistributions_iSup _ (fun n => (c n).2.1) (fun _ _ h => c.monotone h),
    isLinear_iSup _ (fun n => (c n).2.2) (fun _ _ h => c.monotone h)⟩
  le_ωSup c n := show (c n).1 ≤ ⨆ k, (c k).1 from le_iSup (fun k => (c k).1) n
  ωSup_le c T h := show (⨆ n, (c n).1) ≤ T.1 from iSup_le h

end

end InferenceProof.Denotational
