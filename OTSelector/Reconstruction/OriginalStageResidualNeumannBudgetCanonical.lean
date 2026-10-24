import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetCurrentInput
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutCanonical
import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridge

/-! Actual stage densities have one same-scene Neumann bound with no supplied current identity. -/
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

/-- The actual original stage coefficient uses its actual omitted current, actual full
current face trace and actual two full-input reflected response norms, all on the same Q_R. -/
def originalCanonicalStageNeumannBudget (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    (R ell s t : ℝ) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  originalStageCurrentInputNeumannBudget K R s t
    (fun z ↦ originalSeedPathClockSetCurrent S w
      (fun x ↦ originalEuclideanMollifier _ (x-z)) (Ioc s t) scene)
    (fun z ↦ originalRetainedSeedPathClockSetCurrent S w R ell
      (fun x ↦ originalEuclideanMollifier _ (x-z)) (Ioc s t) scene) scene

omit [BorelSpace E] in
/-- The actual original stage coefficient is nonnegative on its physical cube. -/
theorem originalCanonicalStageNeumannBudget_nonneg (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    {R : ℝ} (hR : 0 ≤ R) (ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    0 ≤ originalCanonicalStageNeumannBudget S w K R ell s t scene :=
  originalStageCurrentInputNeumannBudget_nonneg K hR s t _ _ scene

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- One original-scene event controls every actual reserve choice and every mean-zero
smooth stage test. Actual retained/omitted traffic supplies C1 and divergence, actual
geometry removes the retained face trace, and the literal positive-slab identity yields
exactly the original f-g density. No finished stage bound or current identity is assumed. -/
theorem ae_all_originalCanonicalStageResidualDensity_Neumann_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R)
    {s t : ℝ} (hst : s ≤ t) (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ)) :
    let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageResidualDensityData S w R ell η, A.scene = scene →
      ∀ φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ),
        (∫ z in haarRootCube _ R, φ z) = 0 →
      (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z)^2 ≤
        originalCanonicalStageNeumannBudget S w K R ell s t scene *
          ‖smoothPhysicalGradientLtwo K (volume.restrict (haarRootCube _ R)) φ‖^2 := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  have hRone : 1 ≤ R := by linarith
  let η := originalEuclideanMollifier (finrank ℝ S.covector.ker)
  have hη : ContDiff ℝ 1 η := (contDiff_originalEuclideanMollifier _).of_le (by norm_num)
  have hcη : HasCompactSupport η := hasCompactSupport_originalEuclideanMollifier _
  filter_upwards [D.ae_all_originalCanonicalStageResidualDensity_Neumann_readout hF hw Q hell hR hst,
    D.ae_all_originalOmittedCurrent_spatially_contDiff_divergence hF hw hbounds Q,
    D.ae_all_originalClockSetCurrent_spatially_contDiff hF hw hbounds Q,
    D.ae_all_originalRetainedCurrent_eq_zero_on_cube_faces hF hw Q hell hR,
    Q.ae_all_originalStageCurrentInput_Neumann_bound K hq hRone s t]
      with scene hstage hom hfull hret hbudget
  intro A hA φ hm
  let Jfull := fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc s t) scene
  let Jret := fun z ↦ originalRetainedSeedPathClockSetCurrent S w R ell
    (fun x ↦ η (x-z)) (Ioc s t) scene
  have hd := hom R ell s t η hη hcη
  have hb := hbudget Jfull Jret (hfull (Ioc s t) η hη hcη) hd.1
    (hret η (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range _))
      (Ioc s t)) φ hm
  have he : (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
      originalStageCurrentInputPairing R s t Jfull Jret scene φ := by
    rw [hstage.2 A hA K φ hm]
    unfold originalStageCurrentInputPairing
    congr 2
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    change originalOmittedSmoothedSlabDerivative S w R ell s t η z scene * φ z = _
    rw [hd.2 z]
    rfl
  rw [he]
  exact hb

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
