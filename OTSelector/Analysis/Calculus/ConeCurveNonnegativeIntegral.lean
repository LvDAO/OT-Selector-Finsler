import OTSelector.Analysis.Calculus.ConeCurveOccupation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConeCurveNonnegativeTraffic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConeCurveNonnegativeTraffic`; the selected original proof blocks follow. -/
section

/-!
Conditions: A differentiable quarter-cone curve and an arbitrary nonnegative edge readout pointwise dominated by its actual speed and vanishing outside a ball.

Objects: Nonnegative occupation bounds retaining radius and length-speed factors, even for arbitrary restrictions.

Proof detail: Apply monotonicity of the nonnegative integral, the cone speed bound and the deterministic residence-time estimate; handle zero speed directly.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Sheldon Axler, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88 (https://measure.axler.net/MIRA.pdf#page=99); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19).
Relation: ENNReal/restricted-readout version of the elementary cone-occupation estimate; it does not add readout measurability beyond the signature.
-/

/-!
# Literal nonnegative traffic on a physical cone curve

The occupation bound also holds directly for the nonnegative edge readout used
by Campbell. Arbitrary restrictions of the actual edge contribution are allowed;
the estimate assumes only pointwise domination by its actual physical speed.
-/

open Set MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal nonnegative restricted contribution is controlled by its true ball time. -/
theorem coneCurve_lintegral_le_ball_time {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {f : ℝ → ℝ≥0∞} (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, f t ≤ ENNReal.ofReal (M * ‖dX t‖))
    (hfR : ∀ t ∈ Icc a b, R < ‖X t‖ → f t = 0) :
    (∫⁻ t in Icc a b, f t) ≤
      ENNReal.ofReal ((5 / 4 : ℝ) * ‖v‖ * M) * volume (Icc a b ∩ {t | ‖X t‖ ≤ R}) := by
  let A := Icc a b ∩ {t | ‖X t‖ ≤ R}
  have hcont : ContinuousOn X (Icc a b) :=
    fun t ht ↦ (hX t ht).continuousAt.continuousWithinAt
  have hA : MeasurableSet A :=
    (hcont.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic).measurableSet
  have hbound : ∀ t ∈ Icc a b, f t ≤
      A.indicator (fun _ ↦ ENNReal.ofReal ((5 / 4 : ℝ) * ‖v‖ * M)) t := by
    intro t ht
    by_cases hr : ‖X t‖ ≤ R
    · rw [indicator_of_mem (show t ∈ A from ⟨ht,hr⟩)]
      exact (hf t ht).trans (ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_left (coneCurve_speed_upper hcone ht) hM
        nlinarith))
    · rw [hfR t ht (lt_of_not_ge hr)]
      exact bot_le
  have hh := lintegral_mono_ae (μ := volume.restrict (Icc a b))
    (ae_restrict_of_forall_mem measurableSet_Icc hbound)
  have hAI : A ∩ Icc a b = A := inter_eq_left.mpr inter_subset_left
  simpa only [lintegral_indicator hA, lintegral_const, Measure.restrict_apply hA,
    hAI, Measure.restrict_apply_univ] using hh

/-- The unchanged nonnegative one-edge traffic is bounded even at zero velocity. -/
theorem coneCurve_lintegral_le_const {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {f : ℝ → ℝ≥0∞} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, f t ≤ ENNReal.ofReal (M * ‖dX t‖))
    (hfR : ∀ t ∈ Icc a b, R < ‖X t‖ → f t = 0) :
    (∫⁻ t in Icc a b, f t) ≤ ENNReal.ofReal ((10 / 3 : ℝ) * M * R) := by
  have hh := coneCurve_lintegral_le_ball_time hX hcone hM hf hfR
  by_cases hv : ‖v‖ = 0
  · simpa only [hv, mul_zero, zero_mul, ENNReal.ofReal_zero] using hh.trans
      (show ENNReal.ofReal ((5 / 4 : ℝ) * ‖v‖ * M) *
        volume (Icc a b ∩ {t | ‖X t‖ ≤ R}) ≤ ENNReal.ofReal ((10 / 3 : ℝ) * M * R) by
        rw [hv, mul_zero, zero_mul, ENNReal.ofReal_zero, zero_mul]
        exact bot_le)
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have htime := coneCurve_ball_time_le (convex_Icc a b) hX hcone hvpos hR
    calc
      _ ≤ ENNReal.ofReal ((5 / 4 : ℝ) * ‖v‖ * M) *
          ENNReal.ofReal (2 * R / ((3 / 4 : ℝ) * ‖v‖)) := hh.trans (by gcongr)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- The exact nonnegative contribution keeps its interval-length and small-speed factor. -/
theorem coneCurve_lintegral_le_length_speed {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (_hab : a ≤ b) (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {f : ℝ → ℝ≥0∞} (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, f t ≤ ENNReal.ofReal (M * ‖dX t‖))
    (hfR : ∀ t ∈ Icc a b, R < ‖X t‖ → f t = 0) :
    (∫⁻ t in Icc a b, f t) ≤ ENNReal.ofReal ((5 / 4 : ℝ) * M * ((b - a) * ‖v‖)) := by
  have hh := coneCurve_lintegral_le_ball_time hX hcone hM hf hfR
  calc
    _ ≤ ENNReal.ofReal ((5 / 4 : ℝ) * ‖v‖ * M) * volume (Icc a b) :=
      hh.trans (by
        apply mul_le_mul_right
        exact measure_mono inter_subset_left)
    _ = _ := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- The literal nonnegative readout has a min-one bound, including zero-length windows. -/
theorem coneCurve_lintegral_le_min_one {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hab : a ≤ b) (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {f : ℝ → ℝ≥0∞} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b, f t ≤ ENNReal.ofReal (M * ‖dX t‖))
    (hfR : ∀ t ∈ Icc a b, R < ‖X t‖ → f t = 0) :
    (∫⁻ t in Icc a b, f t) ≤
      ENNReal.ofReal ((4 * M * (R + 1)) * min 1 ((b - a) * ‖v‖)) := by
  have hconst := coneCurve_lintegral_le_const hX hcone hR hM hf hfR
  have hsmall := coneCurve_lintegral_le_length_speed hab hX hcone hM hf hfR
  have hCMR : (10 / 3 : ℝ) * M * R ≤ 4 * M * (R + 1) := by
    nlinarith [mul_nonneg hM hR]
  have hCM : (5 / 4 : ℝ) * M ≤ 4 * M * (R + 1) := by
    nlinarith [mul_nonneg hM hR]
  by_cases h : (b - a) * ‖v‖ ≤ 1
  · rw [min_eq_right h]
    exact hsmall.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCM
      (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg _))))
  · rw [min_eq_left (le_of_not_ge h), mul_one]
    exact hconst.trans (ENNReal.ofReal_le_ofReal hCMR)

end OTSelector.Reconstruction

end
end
