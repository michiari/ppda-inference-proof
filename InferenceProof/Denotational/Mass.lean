module

public import InferenceProof.DenotationalSemantics
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Order.FixedPoints

set_option linter.style.header false

/-! # Nonnegative kernels and increasing limits

The sum/product limit rules of Appendix A, Lemma `lem:op-seq`, are used in
their extended-nonnegative-real form. No finiteness assumption is needed here.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Denotational

noncomputable section

variable {α β γ : Type*}

@[simp] theorem totalMass_zero : totalMass (0 : Mass α) = 0 := by
  simp only [totalMass, Pi.zero_apply, tsum_zero]

@[simp] theorem totalMass_dirac (a : α) : totalMass (dirac a) = 1 := by
  classical
  simp [totalMass, dirac]

theorem isSubdistribution_zero : IsSubdistribution (0 : Mass α) := by
  simp only [IsSubdistribution, totalMass_zero, zero_le_one]

theorem isSubdistribution_dirac (a : α) : IsSubdistribution (dirac a) := by
  simp only [IsSubdistribution, totalMass_dirac, le_refl]

@[simp] theorem bind_dirac (a : α) (K : α → Mass β) : bind (dirac a) K = K a := by
  classical
  funext b
  simp [bind, dirac]

@[simp] theorem bind_dirac_right (p : Mass α) : bind p dirac = p := by
  classical
  funext a
  simp [bind, dirac]

@[simp] theorem bind_zero (K : α → Mass β) : bind 0 K = 0 := by
  funext b
  simp only [bind, Pi.zero_apply, zero_mul, tsum_zero]

@[simp] theorem bind_zero_right (p : Mass α) : bind p (fun _ => (0 : Mass β)) = 0 := by
  funext b
  simp only [bind, Pi.zero_apply, mul_zero, tsum_zero]

theorem bind_assoc (p : Mass α) (K : α → Mass β) (L : β → Mass γ) :
    bind (bind p K) L = bind p (fun a => bind (K a) L) := by
  funext c
  simp only [bind, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
  exact ENNReal.tsum_comm

theorem bind_add (p q : Mass α) (K : α → Mass β) :
    bind (p + q) K = bind p K + bind q K := by
  funext b
  simp only [bind, Pi.add_apply, add_mul, ENNReal.tsum_add]

theorem bind_add_right (p : Mass α) (K L : α → Mass β) :
    bind p (fun a => K a + L a) = bind p K + bind p L := by
  funext b
  simp only [bind, Pi.add_apply, mul_add, ENNReal.tsum_add]

theorem totalMass_bind (p : Mass α) (K : α → Mass β) :
    totalMass (bind p K) = ∑' a, p a * totalMass (K a) := by
  simp only [totalMass, bind, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem totalMass_add (p q : Mass α) : totalMass (p + q) = totalMass p + totalMass q :=
  ENNReal.tsum_add

theorem totalMass_mul (r : ℝ≥0∞) (p : Mass α) :
    totalMass (fun a => r * p a) = r * totalMass p :=
  ENNReal.tsum_mul_left

theorem totalMass_bind_le (p : Mass α) (K : α → Mass β)
    (hK : ∀ a, IsSubdistribution (K a)) : totalMass (bind p K) ≤ totalMass p := by
  rw [totalMass_bind]
  apply ENNReal.tsum_le_tsum
  intro a
  exact (mul_le_mul' le_rfl (hK a)).trans_eq (mul_one _)

theorem IsSubdistribution.bind {p : Mass α} (hp : IsSubdistribution p)
    {K : α → Mass β} (hK : ∀ a, IsSubdistribution (K a)) : IsSubdistribution (bind p K) :=
  (totalMass_bind_le p K hK).trans hp

theorem totalMass_map (f : α → β) (p : Mass α) : totalMass (map f p) = totalMass p := by
  simp only [map, totalMass_bind, totalMass_dirac, mul_one]
  rfl

theorem IsSubdistribution.map {p : Mass α} (hp : IsSubdistribution p) (f : α → β) :
    IsSubdistribution (map f p) := by
  simpa only [IsSubdistribution, totalMass_map] using hp

theorem bind_mono {p q : Mass α} {K L : α → Mass β} (hp : p ≤ q) (hK : K ≤ L) :
    bind p K ≤ bind q L := by
  intro b
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (hp a) (hK a b)

/-- Increasing nonnegative sums commute with increasing suprema. -/
theorem tsum_iSup_of_monotone (f : ℕ → α → ℝ≥0∞) (hf : Monotone f) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  classical
  calc
    _ = ⨆ s : Finset α, ∑ a ∈ s, ⨆ n, f n a := ENNReal.tsum_eq_iSup_sum
    _ = ⨆ n, ⨆ s : Finset α, ∑ a ∈ s, f n a := by
      simp_rw [ENNReal.finsetSum_iSup_of_monotone (fun a i j h => hf h a)]
      rw [iSup_comm]
    _ = _ := by simp_rw [← ENNReal.tsum_eq_iSup_sum]

/-- Appendix A, Lemma `lem:double-index`, in any complete lattice. -/
theorem iSup_diagonal {L : Type*} [CompleteLattice L] (a : ℕ → ℕ → L)
    (h₁ : ∀ j, Monotone (fun i => a i j)) (h₂ : ∀ i, Monotone (a i)) :
    (⨆ i, ⨆ j, a i j) = ⨆ n, a n n := by
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    exact le_iSup_of_le (max i j)
      ((h₁ j (Nat.le_max_left i j)).trans (h₂ _ (Nat.le_max_right i j)))
  · exact iSup_le fun n => le_iSup_of_le n (le_iSup (a n) n)

theorem iSup_mul_of_monotone {f g : ℕ → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n) * (⨆ n, g n) = ⨆ n, f n * g n := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  exact iSup_diagonal _ (fun _ _ _ h => mul_le_mul' (hf h) le_rfl)
    (fun _ _ _ h => mul_le_mul' le_rfl (hg h))

theorem bind_iSup (p : ℕ → Mass α) (K : ℕ → α → Mass β)
    (hp : Monotone p) (hK : Monotone K) :
    bind (⨆ n, p n) (⨆ n, K n) = ⨆ n, bind (p n) (K n) := by
  funext b
  simp only [bind, iSup_apply]
  simp_rw [iSup_mul_of_monotone (fun _ _ h => hp h _) (fun _ _ h => hK h _ b)]
  exact tsum_iSup_of_monotone _ (fun _ _ h a => mul_le_mul' (hp h a) (hK h a b))

theorem totalMass_iSup (p : ℕ → Mass α) (hp : Monotone p) :
    totalMass (⨆ n, p n) = ⨆ n, totalMass (p n) := by
  simp only [totalMass, iSup_apply]
  exact tsum_iSup_of_monotone p hp

theorem isSubdistribution_iSup (p : ℕ → Mass α) (hp : Monotone p)
    (h : ∀ n, IsSubdistribution (p n)) : IsSubdistribution (⨆ n, p n) := by
  rw [IsSubdistribution, totalMass_iSup p hp]
  exact iSup_le h

end

end InferenceProof.Denotational
