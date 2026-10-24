import OTSelector.Reconstruction.BirthTrafficPhysicalHaarScale
import OTSelector.Reconstruction.MarkedPhaseBandIntensity

/-! Original Poisson birth bands have intensity of order `s/t` in the same
actual canonical phase frame. The physical Haar factor and density-rank factor
are both proved from the same original residue before they cancel. -/
open Set Function Matrix MeasureTheory
open scoped ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical intensity of the unchanged original birth-band phase cell is
at most `C D K s/t`. The leg determinant bound and original band mass are
geometric intermediate conclusions; no count law or selected-cloud premise enters. -/
theorem exists_birthBand_original_phaseCell_intensity_bound
    {G : Matrix ι ι ℝ} (hG : G.PosSemidef) (hq : 0 < Fintype.card ι) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ) [SFinite μ],
      ∀ {t s D K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 0 ≤ D → 0 ≤ K →
      ∀ {U : ℝ → Matrix ι ι ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (ι → ℝ)}, Measurable c → ∀ {B : Set ℝ}, MeasurableSet B →
      (∀ a ∈ B, (1 + U a).det ≤ D) → μ B ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      ((volume : Measure (ι → ℝ)).prod μ)
        (markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R) ≤
          ENNReal.ofReal (C * D * K * (s / t)) := by
  obtain ⟨Cf, hCf, hframe⟩ := exists_birthTrafficSpatialFrame_det_bound hG hq
  let V : ℝ := (volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R))).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hVfin : volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) ≠ ∞ :=
    (isCompact_closedBall _ _).measure_ne_top
  have hVeq : volume (Metric.closedBall (0 : ι → ℝ) (phaseSourceCellRadius ι R)) = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal hVfin).symm
  refine ⟨Cf * V + 1, by positivity, fun μ _ {t s D K} ht ht1 hs hD hK {U} hUm hU {c} hc {B} hB hdet hmass ↦ ?_⟩
  have hb := prod_volume_markedPhaseSourceCell_le_of_band_det_bound
    (birthTrafficSpatialFrame_isUnit_det hG ht hs) hUm hU hc hB μ R hdet hmass
  rw [hVeq] at hb
  have hcoeff : |(birthTrafficSpatialFrame G t s).det| * V * D * (K * t ^ G.rank * s) ≤
      (Cf * V) * D * K * (s / t) := by
    calc
      _ ≤ (Cf * (t ^ (G.rank + 1))⁻¹) * V * D * (K * t ^ G.rank * s) := by
        gcongr
        exact hframe t s ht ht1 hs
      _ = _ := by rw [pow_succ]; field_simp
  calc
    _ ≤ (ENNReal.ofReal |(birthTrafficSpatialFrame G t s).det| * ENNReal.ofReal V) *
        ENNReal.ofReal D * ENNReal.ofReal (K * t ^ G.rank * s) := hb
    _ = ENNReal.ofReal (|(birthTrafficSpatialFrame G t s).det| * V * D * (K * t ^ G.rank * s)) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hV),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _) hV) hD)]
    _ ≤ ENNReal.ofReal ((Cf * V) * D * K * (s / t)) := ENNReal.ofReal_le_ofReal hcoeff
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith

end OTSelector.Reconstruction
