import OTSelector.Reconstruction.MarkedPhaseSourceCellVolume

/-! Local original phase-cell intensities on narrow clock bands. Exact physical
Haar determinants and original clock masses are retained. -/
open Set Function Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A determinant bound on the actual band bounds its literal marked phase-cell
intensity by the exact Haar factor times the original band mass. -/
theorem prod_volume_markedPhaseSourceCell_le_of_band_det_bound
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ) {D m : ℝ}
    (hdet : ∀ a ∈ B, (1 + U a).det ≤ D) (hmass : μ B ≤ ENNReal.ofReal m) :
    ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B R) ≤
      (ENNReal.ofReal |L.det| *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
      ENNReal.ofReal D * ENNReal.ofReal m := by
  rw [prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ R]
  have hI : (∫⁻ a, ENNReal.ofReal (B.indicator (fun a ↦ (1 + U a).det) a) ∂μ) ≤
      ENNReal.ofReal D * μ B := by
    calc
      _ ≤ ∫⁻ a, B.indicator (fun _ ↦ ENNReal.ofReal D) a ∂μ := by
        apply lintegral_mono
        intro a
        by_cases ha : a ∈ B
        · simpa only [indicator_of_mem ha] using ENNReal.ofReal_le_ofReal (hdet a ha)
        · simp only [indicator_of_notMem ha, ENNReal.ofReal_zero, le_refl]
      _ = _ := by rw [lintegral_indicator hB]; simp
  calc
    _ ≤ (ENNReal.ofReal |L.det| *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
          (ENNReal.ofReal D * μ B) := by gcongr
    _ ≤ (ENNReal.ofReal |L.det| *
        volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
          (ENNReal.ofReal D * ENNReal.ofReal m) := by gcongr
    _ = _ := by ac_rfl

/-- All factors in the narrow-band phase intensity are finite, including the
actual physical Haar volume, even if the whole source envelope is unbounded. -/
theorem phaseBandIntensity_bound_ne_top
    (L : Matrix ι ι ℝ) (R D m : ℝ) :
    (ENNReal.ofReal |L.det| *
      volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))) *
      ENNReal.ofReal D * ENNReal.ofReal m ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (isCompact_closedBall _ _).measure_ne_top
    · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

end OTSelector.Reconstruction
