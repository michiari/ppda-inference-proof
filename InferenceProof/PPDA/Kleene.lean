module

public import InferenceProof.PPDA.Polynomial

set_option linter.style.header false

/-!
# Iterating the termination polynomials

The least solution is the supremum of finite polynomial approximations. This
establishes the fixed-point construction independently of the path semantics.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

private theorem iSup_mul_iSup_of_monotone {f g : ℕ → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) :
    (⨆ n, f n) * (⨆ n, g n) = ⨆ n, f n * g n := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    exact le_iSup_of_le (max i j)
      (mul_le_mul' (hf (Nat.le_max_left i j)) (hg (Nat.le_max_right i j)))
  · exact iSup_le fun n => le_iSup_of_le n (le_iSup (fun j => f n * g j) n)

private theorem sum_iSup_of_monotone {ι : Type*} (s : Finset ι)
    (f : ℕ → ι → ℝ≥0∞) (hf : ∀ i, Monotone fun n => f n i) :
    (∑ i ∈ s, ⨆ n, f n i) = ⨆ n, ∑ i ∈ s, f n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, iSup_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [ih, ENNReal.iSup_add_iSup_of_monotone (hf i)]
    intro a b hab
    exact Finset.sum_le_sum fun j _ => hf j hab

variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

/-- Finite sums and products of nonnegative coefficients preserve increasing suprema. -/
theorem polynomial_iSup
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞)
    (x : ℕ → Summary Q Γ) (hx : Monotone x) :
    polynomial weight (⨆ n, x n) = ⨆ n, polynomial weight (x n) := by
  classical
  funext p X q
  simp only [polynomial, iSup_apply]
  have mono_entry (r : Q) (Y : Γ) (t : Q) : Monotone fun n => x n r Y t :=
    fun _ _ h => hx h r Y t
  have mono_quad (r : Q) (Y Z : Γ) (t : Q) :
      Monotone fun n => weight p X r (.two Y Z) * x n r Y t * x n t Z q :=
    fun _ _ h => mul_le_mul' (mul_le_mul' le_rfl (mono_entry r Y t h))
      (mono_entry t Z q h)
  have mono_lin (r : Q) (Y : Γ) :
      Monotone fun n => weight p X r (.one Y) * x n r Y q :=
    fun _ _ h => mul_le_mul' le_rfl (mono_entry r Y q h)
  have quad_sup (r : Q) (Y Z : Γ) (t : Q) :
      weight p X r (.two Y Z) * (⨆ n, x n r Y t) * (⨆ n, x n t Z q) =
        ⨆ n, weight p X r (.two Y Z) * x n r Y t * x n t Z q := by
    rw [ENNReal.mul_iSup (weight p X r (.two Y Z)) (fun n => x n r Y t)]
    exact iSup_mul_iSup_of_monotone
      (fun _ _ h => mul_le_mul' le_rfl (mono_entry r Y t h)) (mono_entry t Z q)
  simp_rw [quad_sup, ENNReal.mul_iSup]
  simp_rw [sum_iSup_of_monotone _ _ (mono_quad _ _ _)]
  have sumZ (r : Q) (Y : Γ) :
      (∑ Z, ⨆ n, ∑ t, weight p X r (.two Y Z) * x n r Y t * x n t Z q) =
        ⨆ n, ∑ Z, ∑ t, weight p X r (.two Y Z) * x n r Y t * x n t Z q :=
    sum_iSup_of_monotone _ _ fun Z a b h =>
      Finset.sum_le_sum fun t _ => mono_quad r Y Z t h
  simp_rw [sumZ]
  have sumY (r : Q) :
      (∑ Y, ⨆ n, ∑ Z, ∑ t, weight p X r (.two Y Z) * x n r Y t * x n t Z q) =
        ⨆ n, ∑ Y, ∑ Z, ∑ t, weight p X r (.two Y Z) * x n r Y t * x n t Z q :=
    sum_iSup_of_monotone _ _ fun Y a b h =>
      Finset.sum_le_sum fun Z _ => Finset.sum_le_sum fun t _ => mono_quad r Y Z t h
  simp_rw [sumY]
  rw [sum_iSup_of_monotone _ _ (fun r a b h =>
    Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun Z _ =>
      Finset.sum_le_sum fun t _ => mono_quad r Y Z t h)]
  simp_rw [sum_iSup_of_monotone _ _ (mono_lin _)]
  rw [sum_iSup_of_monotone _ _ (fun r a b h =>
    Finset.sum_le_sum fun Y _ => mono_lin r Y h)]
  rw [ENNReal.iSup_add_iSup_of_monotone, ENNReal.iSup_add]
  · intro a b h
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ =>
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => mono_quad _ _ _ _ h
  · intro a b h
    exact Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => mono_lin _ _ h

/-- The finite approximation obtained after `n` polynomial iterations from zero. -/
noncomputable def approximation
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) (n : ℕ) : Summary Q Γ :=
  (polynomial weight)^[n] ⊥

@[simp] theorem approximation_succ
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) (n : ℕ) :
    approximation weight (n + 1) = polynomial weight (approximation weight n) := by
  simp only [approximation, Function.iterate_succ_apply']

/-- Polynomial approximations increase with the iteration bound. -/
theorem approximation_monotone
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) :
    Monotone (approximation weight) :=
  (polynomial_monotone weight).monotone_iterate_of_le_map bot_le

/-- Every finite approximation lies below any pre-fixed candidate. -/
theorem approximation_le
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) {x : Summary Q Γ}
    (hx : polynomial weight x ≤ x) (n : ℕ) : approximation weight n ≤ x := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [approximation_succ]
    exact ((polynomial_monotone weight) ih).trans hx

/-- Kleene's characterization for the pPDA termination system. -/
theorem leastSolution_eq_iSup_approximation
    (weight : Q → Γ → Q → Replacement Γ → ℝ≥0∞) :
    leastSolution weight = ⨆ n, approximation weight n := by
  apply le_antisymm
  · apply leastSolution_le
    rw [polynomial_iSup weight _ (approximation_monotone weight)]
    exact iSup_le fun n => le_iSup_of_le (n + 1) (approximation_succ weight n).ge
  · exact iSup_le fun n => approximation_le weight (polynomial_leastSolution weight).le n

end InferenceProof.PPDA
