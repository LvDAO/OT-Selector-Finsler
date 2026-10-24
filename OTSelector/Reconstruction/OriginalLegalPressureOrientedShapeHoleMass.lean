import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeInnerLaw

/-! The literal complementary hole mass under the original unit sampler. -/
open Set Function MeasureTheory
open OTSelector.Probability

noncomputable section
namespace OTSelector.Reconstruction

/-- The sampler's hole mass is exactly the missing oriented-cube volume. -/
theorem originalOrientedShapeUnitHole_real_mass
    {q : ℕ} (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 ≤ s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1 / 2)) :
    (cubeMeasure (Fin q) 1).real (originalOrientedShapeUnitInner b s)ᶜ = 1 - s ^ q := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  rw [measureReal_compl (measurableSet_originalOrientedShapeUnitInner b s), probReal_univ,
    measureReal_def, originalOrientedShapeUnitInner_mass b hs hsub,
    ENNReal.toReal_ofReal (pow_nonneg hs q)]

end OTSelector.Reconstruction
