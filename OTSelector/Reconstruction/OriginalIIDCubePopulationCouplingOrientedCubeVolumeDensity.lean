import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolumeEuclidean

/-! Literal n/V density of the actual population target on the same physical cube. -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {q n : ℕ}

/-- Multiplicity n times the actual normalized physical cube law is exactly
the literal constant n/V density on that same oriented raw cube. -/
theorem originalOrientedCubePopulationTarget_eq_density
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (n : ℕ)
    {R : ℝ} (hR : 0 < R) :
    (n : ℝ≥0∞) • normalizedFiniteLaw (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) =
      (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))).withDensity
        (fun _ ↦ ENNReal.ofReal ((n : ℝ) / volume.real (originalCenteredPhysicalCubeRegion b (2*R)))) := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  have hVfin : volume K ≠ ∞ := by
    rw [volume_originalOrientedTraffic_cube b R, volume_haarRootCube (Fin q) hR.le]
    exact ENNReal.ofReal_ne_top
  have hVpos : volume K ≠ 0 := by
    rw [volume_originalOrientedTraffic_cube b R, volume_haarRootCube (Fin q) hR.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) _)).ne'
  have hVrpos : 0 < volume.real K := ENNReal.toReal_pos hVpos hVfin
  have hcoef : ENNReal.ofReal ((n : ℝ) / volume.real K) = (n : ℝ≥0∞) * (volume K)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hVrpos, ENNReal.ofReal_natCast,
      show ENNReal.ofReal (volume.real K) = volume K from ENNReal.ofReal_toReal hVfin]
    rfl
  rw [normalizedFiniteLaw_restrict_eq_cond volume _ hVfin]
  change (n : ℝ≥0∞) • ((volume K)⁻¹ • volume.restrict K) = _
  rw [withDensity_const, smul_smul]
  exact congrArg (fun c : ℝ≥0∞ ↦ c • volume.restrict K) hcoef.symm

/-- The true Euclidean plan has precisely the original raw n/V physical
population density, read through the standard Euclidean equivalence. -/
theorem originalOrientedEuclideanCubePopulationCoupling_target_density
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (x : Fin n → (Fin q → ℝ)) (hx : ∀ i, x i ∈ OTSelector.Probability.unitCube q) :
    (originalOrientedEuclideanCubePopulationCoupling b R x).map Prod.snd =
      ((volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))).withDensity
        (fun _ ↦ ENNReal.ofReal ((n : ℝ) / volume.real (originalCenteredPhysicalCubeRegion b (2*R))))).map
          (EuclideanSpace.equiv (Fin q) ℝ).symm := by
  rw [(originalOrientedEuclideanCubePopulationCoupling_spec b hR x hx).2.2,
    ← Measure.map_smul, originalOrientedCubePopulationTarget_eq_density b n hR]

end OTSelector.Reconstruction
