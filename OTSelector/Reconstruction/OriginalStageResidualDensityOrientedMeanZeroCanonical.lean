import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedData
import OTSelector.Transport.DensityNeumannInterpolation

/-! Actual same-frame gamma and reserve constants vanish against every mean-zero test. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal ContDiff Topology Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The genuine nonconstant stage core retains both actual omitted cuts and actual ports. -/
def originalOrientedStageResidualCoreDensity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOrientedOmittedCutDensity S w b R ell s scene z +
    originalOrientedStageReflectedClassDensity b R (Ico s t)
      (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
        (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst z -
  originalOrientedOmittedCutDensity S w b R ell t scene z -
    originalOrientedStageReflectedClassDensity b R (Ioc s t)
      (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
        (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd z

namespace OriginalOrientedStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
  (A : OriginalOrientedStageResidualDensityData S w b R ell)

omit [BorelSpace E] in
/-- Literal gamma and surviving-reserve terms are spatial constants on the same cube;
their pairing vanishes by mean zero without count balance, floor or cut cancellation. -/
theorem meanZero_test_pairing {s t : ℝ}
    (hcore : Integrable (originalOrientedStageResidualCoreDensity S w b R ell s t A.scene) A.cubeMeasure)
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ))
    (hm : (∫ z, φ z ∂A.cubeMeasure) = 0) :
    (∫ z, (A.sourceDensity s t z - A.targetDensity s t z) * φ z ∂A.cubeMeasure) =
      ∫ z, originalOrientedStageResidualCoreDensity S w b R ell s t A.scene z * φ z ∂A.cubeMeasure := by
  let core := originalOrientedStageResidualCoreDensity S w b R ell s t A.scene
  let c := A.gamma s - A.gamma t +
    (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume -
    (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume
  have hcoreφ : Integrable (fun z ↦ core z * φ z) A.cubeMeasure := by
    simpa only [mul_comm] using smoothTest_mul_density_integrable K A.cubeMeasure φ hcore
  have hφ : Integrable φ A.cubeMeasure :=
    φ.continuous.continuousOn.integrableOn_compact (isCompact_originalStagePhysicalCube b (2 * R))
  have heq : (fun z ↦ (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
      fun z ↦ core z * φ z + c * φ z := by
    funext z
    dsimp [sourceDensity, targetDensity, core, originalOrientedStageResidualCoreDensity,
      sourcePortMeasure, targetPortMeasure, c]
    ring
  rw [heq, integral_add hcoreφ (hφ.const_mul c), integral_const_mul, hm, mul_zero, add_zero]

end OriginalOrientedStageResidualDensityData
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- One actual scene event supplies core integrability and removes all reserve/gamma
constants uniformly over every original reserve array, kept index set and mean-zero test. -/
theorem ae_all_originalOrientedStageResidualDensity_meanZero_test_pairing
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell s t : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) (hRone : 1 ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (originalOrientedStageResidualCoreDensity S w b R ell s t scene)
        (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) ∧
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell, A.scene = scene →
      ∀ (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ)),
        (∫ z, φ z ∂A.cubeMeasure) = 0 →
      (∫ z, (A.sourceDensity s t z - A.targetDensity s t z) * φ z ∂A.cubeMeasure) =
        ∫ z, originalOrientedStageResidualCoreDensity S w b R ell s t scene z * φ z ∂A.cubeMeasure := by
  filter_upwards [D.ae_all_originalOrientedStagePortDensities_integrable_mass hF hw Q b hell hR hRone,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell s,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell t] with scene hp hs ht
  have hc : Integrable (originalOrientedStageResidualCoreDensity S w b R ell s t scene)
      (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) :=
    ((hs.add (hp (Ico s t)).1.1).sub ht).sub (hp (Ioc s t)).2.1
  refine ⟨hc, ?_⟩
  intro A hA K φ hm
  have hcA : Integrable (originalOrientedStageResidualCoreDensity S w b R ell s t A.scene) A.cubeMeasure := by
    rw [hA]
    exact hc
  simpa only [hA] using A.meanZero_test_pairing hcA K φ hm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
