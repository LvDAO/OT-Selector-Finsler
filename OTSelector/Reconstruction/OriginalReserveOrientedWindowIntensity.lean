import OTSelector.Reconstruction.OriginalReserveOrientedWindowDilation
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveIntensity

/-! The same preimage-window original reserve count has its actual physical intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original preimage-window Poisson rate is precisely the actual dilation
Jacobian times the volume of the same physical cube. -/
theorem originalOrientedReservePreimage_count_rate {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    (volume (originalCenteredPhysicalCubeRegion b (2 * (R / c)))).toNNReal =
      Real.toNNReal |(c ^ q)⁻¹| *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal := by
  have hcalc : (2 * (R / c)) ^ q = |(c ^ q)⁻¹| * (2 * R) ^ q := by
    rw [show 2 * (R / c) = (2 * R) / c by ring, div_pow,
      abs_of_pos (inv_pos.mpr (pow_pos hc q)), div_eq_mul_inv, mul_comm]
  rw [volume_originalOrientedTraffic_cube b (R / c),
    volume_originalOrientedTraffic_cube b R,
    volume_haarRootCube (Fin q) (div_nonneg hR hc.le),
    volume_haarRootCube (Fin q) hR, Fintype.card_fin]
  simp only [ENNReal.ofReal, ENNReal.toNNReal_coe]
  rw [hcalc, Real.toNNReal_mul (abs_nonneg _)]

/-- The canonical positive reserve dilation gives exactly theta times actual
physical volume as its original Poisson count rate. -/
theorem originalOrientedReserveIntensity_count_rate {q : ℕ} (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ R : ℝ} (hθ : 0 < θ) (hR : 0 ≤ R) :
    (volume (originalCenteredPhysicalCubeRegion b
      (2 * (R / legalIntensityDilation q θ)))).toNNReal =
      Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal := by
  rw [originalOrientedReservePreimage_count_rate b (legalIntensityDilation_pos q hθ) hR,
    legalIntensityDilation_jacobian hq hθ]

end OTSelector.Reconstruction
