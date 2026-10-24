import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationFull

/-! The literal same-frame volume cancels the reserve population energy scale. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- With the actual reserve rate θ times the actual oriented cube volume,
the population energy per unit volume is exactly q C_q θ^(1-2/q). -/
theorem originalReserveBlockClassOrientedPopulation_normalizedRate
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hq : 4 < q) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let rate := Real.toNNReal θ * (volume K).toNNReal
    (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ))) /
      volume.real K = (q : ℝ)*dyadicMatchingConstant q*θ^(1-2/(q : ℝ)) := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  have hL : 0 < 2*R := by positivity
  have hV : volume.real K = (2*R)^q := by
    calc
      _ = volume.real (haarRootCube (Fin q) R) := by
        simpa only [K, measureReal_def] using
          congrArg ENNReal.toReal (volume_originalOrientedTraffic_cube b R)
      _ = _ := by rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
  have hr : ((Real.toNNReal θ * (volume K).toNNReal : ℝ≥0) : ℝ) = θ*volume.real K := by
    simp only [NNReal.coe_mul, Real.coe_toNNReal θ hθ, ENNReal.coe_toNNReal_eq_toReal, measureReal_def]
  have hq₀ : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (q : ℝ)*(1-2/(q : ℝ)) = (q : ℝ)-2 := by field_simp [hq₀]
  have hp : ((2*R)^q : ℝ)^(1-2/(q : ℝ)) = (2*R)^q/(2*R)^2 := by
    rw [← Real.rpow_natCast_mul hL.le, hqr, Real.rpow_sub hL,
      Real.rpow_natCast, Real.rpow_two]
  change (((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*
    (((Real.toNNReal θ * (volume K).toNNReal : ℝ≥0) : ℝ)^(1-2/(q : ℝ)))) /
      volume.real K = _
  rw [hr, Real.mul_rpow hθ measureReal_nonneg, hV, hp]
  field_simp [hL.ne', pow_ne_zero q hL.ne']

namespace OriginalReserveFullUnitInputExperiment
variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- Both actual original-label families in this same full experiment have a
uniform per-volume endpoint energy bound on every true fine-class selection. -/
theorem blockClassOrientedAtomEnergy_normalized (hR : 0 < R) (hq : 4 < q)
    {S T Cs Ct Ds Dt : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hCs : MeasurableSet Cs) (hCt : MeasurableSet Ct)
    (hDs : MeasurableSet Ds) (hDt : MeasurableSet Dt) :
    let J := (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    let V := volume.real (originalCenteredPhysicalCubeRegion b (2*R))
    ((∫ p, originalReserveBlockClassOrientedAtomEnergy b R 0 1 S T Cs Ds
        (originalReserveUnitSourceSamplerView q θ hθ1 p) ∂J) / V ≤
      (q : ℝ)*dyadicMatchingConstant q*θ^(1-2/(q : ℝ))) ∧
    ((∫ p, originalReserveBlockClassOrientedAtomEnergy b R 1 0 S T Ct Dt
        (originalReserveUnitTargetSamplerView q θ hθ1 p) ∂J) / V ≤
      (q : ℝ)*dyadicMatchingConstant q*θ^(1-2/(q : ℝ))) := by
  have hs := X.source_blockClassOrientedAtomLaws hR hq hS hT hCs hDs
  have ht := X.target_blockClassOrientedAtomLaws hR hq hS hT hCt hDt
  have hn := originalReserveBlockClassOrientedPopulation_normalizedRate b hR hθ.le hq
  exact ⟨(div_le_div_of_nonneg_right hs.2.2 measureReal_nonneg).trans_eq hn,
    (div_le_div_of_nonneg_right ht.2.2 measureReal_nonneg).trans_eq hn⟩

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
