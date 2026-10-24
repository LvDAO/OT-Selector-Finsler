import OTSelector.Reconstruction.OriginalStageResidualDensityEqualMass
import OTSelector.Transport.DensityNeumannInterpolation

/-! Literal gamma and reserve constants vanish against actual mean-zero cube tests. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The exact nonconstant stage residual keeps both actual omitted cuts and actual ports. -/
def originalStageResidualCoreDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOmittedCutDensity S w R ell s η z scene +
    originalStageSourcePortDensity S w R ell η (Ico s t) scene z -
    originalOmittedCutDensity S w R ell t η z scene -
    originalStageTargetPortDensity S w R ell η (Ioc s t) scene z

namespace OriginalStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {R ell : ℝ}
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
  (A : OriginalStageResidualDensityData S w R ell η)

omit [BorelSpace E] in
/-- Actual gamma and surviving-reserve terms are spatial constants; their test pairing
vanishes from the given cube mean zero, without a count cancellation or floor assumption. -/
theorem meanZero_test_pairing {s t : ℝ}
    (hcuts : Integrable (fun z ↦ originalOmittedCutDensity S w R ell s η z A.scene)
      (volume.restrict (haarRootCube _ R)))
    (hcutt : Integrable (fun z ↦ originalOmittedCutDensity S w R ell t η z A.scene)
      (volume.restrict (haarRootCube _ R)))
    (hsrc : Integrable (originalStageSourcePortDensity S w R ell η (Ico s t) A.scene)
      (volume.restrict (haarRootCube _ R)))
    (htgt : Integrable (originalStageTargetPortDensity S w R ell η (Ioc s t) A.scene)
      (volume.restrict (haarRootCube _ R)))
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ))
    (hm : (∫ z in haarRootCube _ R, φ z) = 0) :
    (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
      ∫ z in haarRootCube _ R, originalStageResidualCoreDensity S w R ell s t η A.scene z * φ z := by
  let σ := volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)
  let core := originalStageResidualCoreDensity S w R ell s t η A.scene
  let c := A.gamma s - A.gamma t +
    (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume -
    (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume
  have hcore : Integrable core σ := ((hcuts.add hsrc).sub hcutt).sub htgt
  have hcoreφ : Integrable (fun z ↦ core z * φ z) σ := by
    simpa only [mul_comm] using smoothTest_mul_density_integrable K σ φ hcore
  have hφ : Integrable φ σ := φ.continuous.continuousOn.integrableOn_Icc
  have heq : (fun z ↦ (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
      fun z ↦ core z * φ z + c * φ z := by
    funext z
    dsimp [sourceDensity, targetDensity, core, originalStageResidualCoreDensity, c]
    ring
  rw [heq, integral_add hcoreφ (hφ.const_mul c), integral_const_mul, hm, mul_zero, add_zero]

end OriginalStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- One original-scene event removes literal stage constants for every actual reserve
observation and all smooth mean-zero tests. All required spatial L1 comes from the original law. -/
theorem ae_all_originalStageResidualDensity_meanZero_test_pairing
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) (hRone : 1 ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) {s t : ℝ} :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageResidualDensityData S w R ell η, A.scene = scene →
      ∀ (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ)),
        (∫ z in haarRootCube _ R, φ z) = 0 →
      (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
        ∫ z in haarRootCube _ R, originalStageResidualCoreDensity S w R ell s t η scene z * φ z := by
  filter_upwards [D.ae_all_originalStagePortDensities_integrable_mass hF hw Q hell hR hRone
      hη hηI hηone hηsupport hηeven hηM,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (show 0 ≤ R by linarith) ell s hη hηM hηsupport,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (show 0 ≤ R by linarith) ell t hη hηM hηsupport]
    with scene hp hs ht
  intro A hA K φ hm
  have hsA := hs
  have htA := ht
  have hsrc := (hp (Ico s t)).1.1
  have htgt := (hp (Ioc s t)).2.1
  rw [← hA] at hsA htA hsrc htgt
  simpa only [hA] using A.meanZero_test_pairing hsA htA hsrc htgt K φ hm

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
