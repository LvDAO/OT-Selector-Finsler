import OTSelector.Probability.FinslerAtlasCubeInputs
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation

/-! Normalized original Haar restrictions in arbitrary measurable coordinates. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
open OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X]

/-- The original restricted Haar mass cancels its coordinate Jacobian. The
coordinate map can be affine; no constancy of a population density is assumed. -/
theorem normalized_haar_coordinate_preimage_cube (q : ℕ)
    (μ : Measure X) {f : X → Fin q → ℝ} (hf : Measurable f)
    {c : ℝ≥0} (hc : 0 < c)
    (hmap : μ.map f = c • (volume : Measure (Fin q → ℝ))) :
    (normalizedFiniteLaw (μ.restrict (f ⁻¹' seedUnitCube q))).map f =
      cubeMeasure (Fin q) 1 := by
  have hrestrict : (μ.restrict (f ⁻¹' seedUnitCube q)).map f =
      c • cubeMeasure (Fin q) 1 := by
    rw [← Measure.restrict_map hf (measurableSet_seedUnitCube q), hmap,
      Measure.restrict_smul, ← cubeMeasure_eq_volume_restrict_seedUnitCube]
  let _instCube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hmass : (μ.restrict (f ⁻¹' seedUnitCube q)).real univ = (c : ℝ) := by
    have hm := congrArg (fun ν : Measure (Fin q → ℝ) ↦ ν univ) hrestrict
    simp only [Measure.map_apply hf MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, Measure.smul_apply, measure_univ] at hm
    simpa [measureReal_def, NNReal.smul_def] using
      congrArg ENNReal.toReal hm
  unfold normalizedFiniteLaw
  rw [hmass, Measure.map_smul, hrestrict, smul_smul]
  have hc0 : c ≠ 0 := ne_of_gt hc
  simp only [Real.toNNReal_inv, Real.toNNReal_coe, inv_mul_cancel₀ hc0, one_smul]

end OTSelector.Probability
