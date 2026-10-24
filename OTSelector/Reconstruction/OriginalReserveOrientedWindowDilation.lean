import OTSelector.Reconstruction.OriginalReserveMappedWindowSampler
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilation

/-! Complementary physical dilation preserves the same oriented reserve cube and every original index. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Dilating the preimage-cube original sample gives exactly the same physical cube point. -/
theorem originalOrientedRawCubePhysicalMap_scale {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : c ≠ 0) (R : ℝ) (v : Fin q → ℝ) :
    c • originalOrientedRawCubePhysicalMap b (R / c) v =
      originalOrientedRawCubePhysicalMap b R v := by
  change c • orthonormalPhysicalCubeMap b (fun i ↦ 2 * (R / c) * v i - R / c) = _
  rw [← map_smul]
  apply congrArg (orthonormalPhysicalCubeMap b)
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hc]

/-- The preimage of the same physical cube under positive reserve dilation is
its actual smaller cube in that same chosen frame. -/
theorem originalOrientedPhysicalCube_dilation_preimage {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : 0 < c) (R : ℝ) :
    (fun x : Fin q → ℝ ↦ c • x) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R) =
      originalCenteredPhysicalCubeRegion b (2 * (R / c)) := by
  ext x
  simp only [originalOrientedTraffic_cube_eq_preimage, mem_preimage, map_smul]
  change ((∀ i, -R ≤ c * ((orthonormalPhysicalCubeMap b).symm x) i) ∧
    (∀ i, c * ((orthonormalPhysicalCubeMap b).symm x) i ≤ R)) ↔
    ((∀ i, -(R / c) ≤ ((orthonormalPhysicalCubeMap b).symm x) i) ∧
      (∀ i, ((orthonormalPhysicalCubeMap b).symm x) i ≤ R / c))
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      have h : (-R) / c ≤ ((orthonormalPhysicalCubeMap b).symm x) i :=
        (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hl i)
      simpa only [neg_div] using h
    · exact fun i ↦ (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hu i)
  · rintro ⟨hl, hu⟩
    constructor
    · intro i
      have h : (-R) / c ≤ ((orthonormalPhysicalCubeMap b).symm x) i := by
        simpa only [neg_div] using hl i
      simpa only [mul_comm] using (div_le_iff₀ hc).mp h
    · exact fun i ↦ by simpa only [mul_comm] using (le_div_iff₀ hc).mp (hu i)

/-- The unchanged clocks and immutable colors do not alter that actual spatial preimage. -/
theorem originalColoredInput_orientedCube_dilation_preimage {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : 0 < c) (R : ℝ) :
    legalColoredInputDilation q c hc.ne' ⁻¹'
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * (R / c)) := by
  ext p
  exact Set.ext_iff.mp (originalOrientedPhysicalCube_dilation_preimage b hc R) p.1.1

/-- Restriction and actual input dilation therefore commute at the same physical window. -/
theorem originalColoredInput_orientedWindow_dilation {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : 0 < c) (R : ℝ) (μ : Measure (LegalColoredInputPoint q)) :
    (μ.map (legalColoredInputDilation q c hc.ne')).restrict
      ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (μ.restrict ((Prod.fst ∘ Prod.fst) ⁻¹'
        originalCenteredPhysicalCubeRegion b (2 * (R / c)))).map
          (legalColoredInputDilation q c hc.ne') := by
  rw [Measure.restrict_map (legalColoredInputDilation q c hc.ne').continuous.measurable
    ((measurableSet_originalOrientedTraffic_cube b R).preimage
      (measurable_fst.comp measurable_fst)),
    originalColoredInput_orientedCube_dilation_preimage b hc R]

end OTSelector.Reconstruction
