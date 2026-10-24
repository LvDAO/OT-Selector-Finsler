import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutMeanZero
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedPoissonDual

/-! Genuine spatial integrability of the actual stage core and full-input reflection errors. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- True original local finiteness and compact-kernel estimates produce L1 of all three
literal fields needed to split the stage test identity into separate integrals. -/
theorem ae_all_originalStageCore_reflectedInputErrors_integrable
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) (hRone : 1 ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ x, |η x| ≤ M) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (originalStageResidualCoreDensity S w R ell s t η scene)
        (volume.restrict (haarRootCube _ R)) ∧
      Integrable (originalClassReflectedInputScalarField η R (Ico s t)
        (legalInputColorMeasure _ scene.2 0)) (volume.restrict (haarRootCube _ R)) ∧
      Integrable (originalClassReflectedInputScalarField η R (Ioc s t)
        (legalInputColorMeasure _ scene.2 1)) (volume.restrict (haarRootCube _ R)) := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [D.ae_all_originalStagePortDensities_integrable_mass hF hw Q hell hR hRone
      hη hηI hηone hηsupport hηeven hηM,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (show 0 ≤ R by linarith)
      ell s hη hηM hηsupport,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (show 0 ≤ R by linarith)
      ell t hη hηM hηsupport,
    Q.ae_finite_reflectedInputOuterWindow R 0, Q.ae_finite_reflectedInputOuterWindow R 1]
    with scene hp hs ht hfinS hfinT
  refine ⟨((hs.add (hp (Ico s t)).1.1).sub ht).sub (hp (Ioc s t)).2.1, ?_, ?_⟩
  · simpa only [mul_one] using
      (integrable_originalClassReflectedInputScalarField_mul_of_finite_outer hη hM hηM
        hηsupport hRone measurableSet_Ico (legalInputColorMeasure _ scene.2 0) hfinS
        (u := fun _ ↦ (1 : ℝ)) continuous_const)
  · simpa only [mul_one] using
      (integrable_originalClassReflectedInputScalarField_mul_of_finite_outer hη hM hηM
        hηsupport hRone measurableSet_Ioc (legalInputColorMeasure _ scene.2 1) hfinT
        (u := fun _ ↦ (1 : ℝ)) continuous_const)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
