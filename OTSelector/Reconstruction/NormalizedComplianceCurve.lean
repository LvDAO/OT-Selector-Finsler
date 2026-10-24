import OTSelector.Reconstruction.MatrixCongruenceIntervalBounds

/-!
# The actual normalized compliance curve

An original matrix kernel with a uniform scaled bound produces, by its unchanged
interval integral and one fixed congruence, a uniformly small Lipschitz mobility
curve. Both orientations of the original clock are included.
-/

open Set Matrix MeasureTheory
open scoped Topology Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The genuine normalized compliance from a fixed cut to an affine clock. -/
def normalizedComplianceCurve (W : ℝ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ)
    (c ell r : ℝ) : Matrix ι ι ℝ :=
  T * (∫ s in c..(c + ell * r), W s) * Tᵀ

/-- Every affine clock with unit parameter remains between its two endpoints. -/
theorem affineClock_mem_uIcc {c ell r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    c + ell * r ∈ uIcc c (c + ell) := by
  rcases le_total 0 ell with he | he
  · rw [uIcc_of_le (by linarith : c ≤ c + ell)]
    constructor <;> nlinarith [mul_nonneg he hr.1, mul_nonneg he (sub_nonneg.mpr hr.2)]
  · rw [uIcc_of_ge (by linarith : c + ell ≤ c)]
    constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr he) hr.1,
      mul_nonneg (neg_nonneg.mpr he) (sub_nonneg.mpr hr.2)]

/-- Subtracting two actual normalized compliances gives their actual intervening leg. -/
theorem normalizedComplianceCurve_sub (W : ℝ → Matrix ι ι ℝ)
    (T : Matrix ι ι ℝ) {c ell r s : ℝ}
    (hW : ContinuousOn W (uIcc c (c + ell)))
    (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    normalizedComplianceCurve W T c ell r - normalizedComplianceCurve W T c ell s =
      T * (∫ u in (c + ell * s)..(c + ell * r), W u) * Tᵀ := by
  have hwr : IntervalIntegrable W volume c (c + ell * r) :=
    (hW.mono (uIcc_subset_uIcc_left (affineClock_mem_uIcc hr))).intervalIntegrable
  have hws : IntervalIntegrable W volume c (c + ell * s) :=
    (hW.mono (uIcc_subset_uIcc_left (affineClock_mem_uIcc hs))).intervalIntegrable
  unfold normalizedComplianceCurve
  rw [← Matrix.sub_mul, ← Matrix.mul_sub,
    intervalIntegral.integral_interval_sub_left hwr hws]

/-- Uniform scaled kernel control gives the genuine two-parameter mobility estimate. -/
theorem norm_normalizedComplianceCurve_sub_le
    (W : ℝ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ) {c ell t B r s : ℝ}
    (ht : 0 < t) (_hB : 0 ≤ B) (hW : ContinuousOn W (uIcc c (c + ell)))
    (hbound : ∀ u ∈ uIcc c (c + ell), ‖t • (T * W u * Tᵀ)‖ ≤ B)
    (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖normalizedComplianceCurve W T c ell r - normalizedComplianceCurve W T c ell s‖ ≤
      (B * |ell| / t) * |r - s| := by
  have hsub : uIcc (c + ell * s) (c + ell * r) ⊆ uIcc c (c + ell) :=
    uIcc_subset_uIcc (affineClock_mem_uIcc hs) (affineClock_mem_uIcc hr)
  have hw : IntervalIntegrable W volume (c + ell * s) (c + ell * r) :=
    (hW.mono hsub).intervalIntegrable
  rw [normalizedComplianceCurve_sub W T hW hr hs]
  calc
    _ ≤ B * |(c + ell * r) - (c + ell * s)| / t :=
      norm_congruence_intervalIntegral_le_scaled T ht hw
        (fun u hu ↦ hbound u (hsub (uIoc_subset_uIcc hu)))
    _ = (B * |ell| / t) * |r - s| := by
      rw [show (c + ell * r) - (c + ell * s) = ell * (r - s) by ring, abs_mul]
      ring

/-- The reference parameter has exactly zero actual compliance. -/
theorem normalizedComplianceCurve_zero (W : ℝ → Matrix ι ι ℝ)
    (T : Matrix ι ι ℝ) (c ell : ℝ) : normalizedComplianceCurve W T c ell 0 = 0 := by
  simp [normalizedComplianceCurve]

/-- The same mobility is uniformly small on the complete unit parameter interval. -/
theorem norm_normalizedComplianceCurve_le
    (W : ℝ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ) {c ell t B r : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hW : ContinuousOn W (uIcc c (c + ell)))
    (hbound : ∀ u ∈ uIcc c (c + ell), ‖t • (T * W u * Tᵀ)‖ ≤ B)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    ‖normalizedComplianceCurve W T c ell r‖ ≤ B * |ell| / t := by
  have hh := norm_normalizedComplianceCurve_sub_le W T ht hB hW hbound hr
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  rw [normalizedComplianceCurve_zero, sub_zero, sub_zero, abs_of_nonneg hr.1] at hh
  exact hh.trans (mul_le_of_le_one_right (by positivity) hr.2)

end OTSelector.Reconstruction
