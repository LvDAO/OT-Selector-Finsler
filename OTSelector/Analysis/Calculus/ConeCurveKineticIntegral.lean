import OTSelector.Analysis.Calculus.ConeCurveOccupation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.ConeCurveKineticTraffic.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.ConeCurveKineticTraffic`; the selected original proof blocks follow. -/
section

/-!
Conditions: A differentiable curve stays in the quarter-cone around a fixed velocity; the nonnegative kernel is bounded and supported in a ball.

Objects: Real kinetic-occupation bounds by ball residence time, radius, interval length times speed and their minimum.

Proof detail: Bound actual speed by five-quarters of the reference speed, use longitudinal monotonicity for ball residence time and combine the two integral bounds.

Sources: Jiří Lebl, Section 5.3.1, Theorem 5.3.1, pp. 200–201 (https://www.jirka.org/ra/realanal.pdf#page=200); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Sheldon Axler, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88 (https://measure.axler.net/MIRA.pdf#page=99).
Relation: Elementary cone/occupation calculation with explicit constants, used by the paper’s short-window traffic method; no stochastic moment estimate is asserted here.
-/

/-!
# The physical one-edge traffic estimate

A true quarter-cone curve contributes a bounded amount of absolute kinetic
traffic through a bounded physical kernel. The same estimate also retains its
small-speed factor, including zero reference velocity and zero-length windows.
-/

open Set MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Traffic is bounded by the true time in the physical kernel's support. -/
theorem coneCurve_traffic_le_ball_time {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {η : V → ℝ} (_hM : 0 ≤ M) (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    (hηR : ∀ z, R < ‖z‖ → η z = 0) :
    (∫ t in Icc a b, ‖dX t‖ * η (X t)) ≤
      ((5 / 4 : ℝ) * ‖v‖ * M) * volume.real (Icc a b ∩ {t | ‖X t‖ ≤ R}) := by
  let A := Icc a b ∩ {t | ‖X t‖ ≤ R}
  have hcont : ContinuousOn X (Icc a b) :=
    fun t ht ↦ (hX t ht).continuousAt.continuousWithinAt
  have hA : MeasurableSet A :=
    (hcont.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic).measurableSet
  have hbound : ∀ t ∈ Icc a b,
      ‖dX t‖ * η (X t) ≤ A.indicator (fun _ ↦ (5 / 4 : ℝ) * ‖v‖ * M) t := by
    intro t ht
    by_cases hr : ‖X t‖ ≤ R
    · rw [indicator_of_mem (show t ∈ A from ⟨ht,hr⟩)]
      exact mul_le_mul (coneCurve_speed_upper hcone ht) (hηM _) (hη0 _) (by positivity)
    · rw [indicator_of_notMem (show t ∉ A from fun h ↦ hr h.2),
        hηR _ (lt_of_not_ge hr), mul_zero]
  have hh := integral_mono_of_nonneg
    (ae_of_all (volume.restrict (Icc a b)) (fun t ↦ mul_nonneg (norm_nonneg _) (hη0 _)))
    ((integrable_const ((5 / 4 : ℝ) * ‖v‖ * M)).indicator hA)
    (ae_restrict_of_forall_mem measurableSet_Icc hbound)
  have hAI : A ∩ Icc a b = A := inter_eq_left.mpr inter_subset_left
  simpa only [integral_indicator_const _ hA, measureReal_restrict_apply hA, hAI,
    smul_eq_mul, mul_comm] using hh

/-- Every original physical one-edge contribution is uniformly bounded, also for v=0. -/
theorem coneCurve_traffic_le_const {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {η : V → ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    (hηR : ∀ z, R < ‖z‖ → η z = 0) :
    (∫ t in Icc a b, ‖dX t‖ * η (X t)) ≤ (10 / 3 : ℝ) * M * R := by
  have hh := coneCurve_traffic_le_ball_time hX hcone hM hη0 hηM hηR
  by_cases hv : ‖v‖ = 0
  · rw [hv, mul_zero, zero_mul, zero_mul] at hh
    exact hh.trans (by positivity)
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have htime := ENNReal.toReal_le_of_le_ofReal (by positivity)
      (coneCurve_ball_time_le (convex_Icc a b) hX hcone hvpos hR)
    calc
      _ ≤ ((5 / 4 : ℝ) * ‖v‖ * M) *
          (2 * R / ((3 / 4 : ℝ) * ‖v‖)) := hh.trans
        (mul_le_mul_of_nonneg_left htime (by positivity))
      _ = _ := by field_simp; ring

/-- The same physical traffic also retains its small interval-length and speed factor. -/
theorem coneCurve_traffic_le_length_speed {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hab : a ≤ b) (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {η : V → ℝ} (hM : 0 ≤ M) (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    (hηR : ∀ z, R < ‖z‖ → η z = 0) :
    (∫ t in Icc a b, ‖dX t‖ * η (X t)) ≤
      (5 / 4 : ℝ) * M * ((b - a) * ‖v‖) := by
  have hh := coneCurve_traffic_le_ball_time hX hcone hM hη0 hηM hηR
  have htime : volume.real (Icc a b ∩ {t | ‖X t‖ ≤ R}) ≤ b - a := by
    have h := ENNReal.toReal_mono (by simp : volume (Icc a b) ≠ ⊤)
      (measure_mono (inter_subset_left : Icc a b ∩ {t | ‖X t‖ ≤ R} ⊆ Icc a b))
    simpa only [Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h
  calc
    _ ≤ ((5 / 4 : ℝ) * ‖v‖ * M) * (b - a) := hh.trans
      (mul_le_mul_of_nonneg_left htime (by positivity))
    _ = _ := by ring

/-- The uniform and small-speed estimates combine into a true min-one bound. -/
theorem coneCurve_traffic_le_min_one {X dX : ℝ → V} {v : V} {a b R M : ℝ}
    (hab : a ≤ b) (hX : ∀ t ∈ Icc a b, HasDerivAt X (dX t) t)
    (hcone : ∀ t ∈ Icc a b, ‖dX t - v‖ ≤ ‖v‖ / 4)
    {η : V → ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    (hηR : ∀ z, R < ‖z‖ → η z = 0) :
    (∫ t in Icc a b, ‖dX t‖ * η (X t)) ≤
      (4 * M * (R + 1)) * min 1 ((b - a) * ‖v‖) := by
  have hconst := coneCurve_traffic_le_const hX hcone hR hM hη0 hηM hηR
  have hsmall := coneCurve_traffic_le_length_speed hab hX hcone hM hη0 hηM hηR
  have hC : 0 ≤ 4 * M * (R + 1) := by positivity
  have hCMR : (10 / 3 : ℝ) * M * R ≤ 4 * M * (R + 1) := by
    nlinarith [mul_nonneg hM hR]
  have hCM : (5 / 4 : ℝ) * M ≤ 4 * M * (R + 1) := by
    nlinarith [mul_nonneg hM hR]
  have hlin := hsmall.trans
    (mul_le_mul_of_nonneg_right hCM (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg _)))
  by_cases h : (b - a) * ‖v‖ ≤ 1
  · rw [min_eq_right h]
    exact hlin
  · rw [min_eq_left (le_of_not_ge h), mul_one]
    exact hconst.trans hCMR

end OTSelector.Reconstruction

end
end
