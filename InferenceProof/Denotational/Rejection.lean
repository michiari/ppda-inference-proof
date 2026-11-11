module

public import InferenceProof.Denotational.Auxiliary

set_option linter.style.header false

/-! # Normalization as the least rejection-loop solution

Section 5, equation `eq:N-fix-point`. Uniqueness is stated on
subdistributions, as in the paper: in the larger extended-real space an
infinite-valued vector can be an additional affine fixed point.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.Denotational

noncomputable section

variable {S : Signature}

theorem IsSubdistribution.apply_le_one {α : Type*} {p : Mass α}
    (hp : IsSubdistribution p) (a : α) : p a ≤ 1 :=
  (ENNReal.le_tsum a).trans hp

theorem IsSubdistribution.apply_ne_top {α : Type*} {p : Mass α}
    (hp : IsSubdistribution p) (a : α) : p a ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hp.apply_le_one a)

theorem successfulMass_le {q : OutputMass S} (hq : IsSubdistribution q) :
    (∑' v, q (some v)) ≤ 1 - q none := by
  apply ENNReal.le_sub_of_add_le_left (hq.apply_ne_top none)
  simpa only [IsSubdistribution, totalMass_option] using hq

theorem eq_dirac_error_of_mass_one {q : OutputMass S} (hq : IsSubdistribution q)
    (h : q none = 1) : q = dirac none := by
  classical
  have hz : (∑' v, q (some v)) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [h, tsub_self, bot_eq_zero] using successfulMass_le hq
  funext outcome
  cases outcome with
  | none => simp only [h, dirac, ite_true]
  | some v =>
    have hv : q (some v) = 0 := le_antisymm ((ENNReal.le_tsum v).trans_eq hz) bot_le
    simpa only [dirac, reduceCtorEq, ite_false] using hv

theorem rejectionFunctional_eq_self_of_certain_rejection {q : OutputMass S}
    (hq : IsSubdistribution q) (h : q none = 1) (retry : OutputMass S) :
    rejectionFunctional q retry = retry := by
  classical
  rw [eq_dirac_error_of_mass_one hq h]
  funext outcome
  cases outcome <;> simp [rejectionFunctional, dirac]

@[simp] theorem normalize_none (q : OutputMass S) : normalize q none = 0 := by
  classical
  unfold normalize
  split_ifs <;> rfl

theorem normalize_isSubdistribution {q : OutputMass S} (hq : IsSubdistribution q) :
    IsSubdistribution (normalize q) := by
  classical
  by_cases h : q none < 1
  · change totalMass _ ≤ 1
    rw [totalMass_option]
    simp only [normalize, h, ite_true, zero_add]
    simp_rw [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    apply (ENNReal.div_le_iff (ne_of_gt (tsub_pos_iff_lt.mpr h))
      (ENNReal.sub_ne_top ENNReal.one_ne_top)).mpr
    simpa only [one_mul] using successfulMass_le hq
  · simp only [normalize, h, ite_false]
    exact isSubdistribution_zero

theorem affine_div_fixedPoint (c a : ℝ≥0∞) (hc : c < 1) :
    a + c * (a / (1 - c)) = a / (1 - c) := by
  have hd₀ : 1 - c ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hc)
  have hdTop : 1 - c ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  calc
    _ = (1 - c) * (a / (1 - c)) + c * (a / (1 - c)) := by
      rw [ENNReal.mul_div_cancel hd₀ hdTop]
    _ = ((1 - c) + c) * (a / (1 - c)) := (add_mul _ _ _).symm
    _ = _ := by rw [tsub_add_cancel_of_le hc.le, one_mul]

/-- With rejection probability below one, every finite affine fixed point is the quotient. -/
theorem affine_fixedPoint_unique (c a x : ℝ≥0∞) (hc : c < 1) (hx : x ≠ ∞)
    (h : a + c * x = x) : x = a / (1 - c) := by
  apply (ENNReal.eq_div_iff (ne_of_gt (tsub_pos_iff_lt.mpr hc))
    (ENNReal.sub_ne_top ENNReal.one_ne_top)).mpr
  rw [ENNReal.sub_mul (fun _ _ => hx), one_mul]
  calc
    x - c * x = (a + c * x) - c * x := congrArg (fun z => z - c * x) h.symm
    _ = a := ENNReal.add_sub_cancel_right (ENNReal.mul_ne_top hc.ne_top hx)

/-- Normalization is itself a rejection-loop fixed point, including certain rejection. -/
theorem normalize_fixedPoint {q : OutputMass S} (hq : IsSubdistribution q) :
    rejectionFunctional q (normalize q) = normalize q := by
  classical
  by_cases h : q none < 1
  · funext outcome
    cases outcome with
    | none => simp only [rejectionFunctional, normalize_none, mul_zero, zero_add]
    | some v =>
      simpa only [rejectionFunctional, normalize, h, ite_true] using
        affine_div_fixedPoint (q none) (q (some v)) h
  · have he : q none = 1 := le_antisymm (hq.apply_le_one none) (le_of_not_gt h)
    rw [eq_dirac_error_of_mass_one hq he]
    funext outcome
    cases outcome <;> simp [rejectionFunctional, dirac, normalize]

/-- The nondegenerate equation has a unique solution among subdistributions. -/
theorem rejection_fixedPoint_unique {q retry : OutputMass S} (hq : q none < 1)
    (hr : IsSubdistribution retry) (hfix : rejectionFunctional q retry = retry) :
    retry = normalize q := by
  classical
  funext outcome
  have h := congrFun hfix outcome
  cases outcome with
  | none =>
    have hn := affine_fixedPoint_unique (q none) 0 (retry none) hq
      (hr.apply_ne_top none) h
    simpa only [ENNReal.zero_div, normalize_none] using hn
  | some v =>
    have hv := affine_fixedPoint_unique (q none) (q (some v)) (retry (some v)) hq
      (hr.apply_ne_top (some v)) h
    simpa only [normalize, hq, ite_true] using hv

theorem normalize_le_fixedPoint {q retry : OutputMass S}
    (hr : IsSubdistribution retry) (hfix : rejectionFunctional q retry = retry) :
    normalize q ≤ retry := by
  classical
  by_cases h : q none < 1
  · exact (rejection_fixedPoint_unique h hr hfix).ge
  · simp only [normalize, h, ite_false]
    exact bot_le

/-- The conditioning operator is the least solution in the paper's subdistribution domain. -/
theorem normalize_isLeast {q : OutputMass S} (hq : IsSubdistribution q) :
    IsLeast {retry : Subdistribution (Outcome S) |
      rejectionFunctional q retry.1 = retry.1}
      ⟨normalize q, normalize_isSubdistribution hq⟩ :=
  ⟨normalize_fixedPoint hq, fun retry hfix => normalize_le_fixedPoint retry.2 hfix⟩

end

end InferenceProof.Denotational
