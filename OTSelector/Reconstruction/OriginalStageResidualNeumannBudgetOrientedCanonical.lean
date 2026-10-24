import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCurrentInput
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedPortReadoutCanonical
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedMeanZeroCanonical

/-! The actual same-frame literal stage densities obey their common physical Neumann bound. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Literal same-frame original stage densities equal their actual omitted-current and
full-input reflection pairing for every mean-zero smooth test on one original-scene event.
Port projections, retained reflection, positive FTC, constants and all L1 are internal. -/
theorem ae_all_originalOrientedStageResidualDensity_currentInput_pairing
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell, A.scene = scene →
      ∀ (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ)),
      (∫ z in originalCenteredPhysicalCubeRegion b (2*R), φ z) = 0 →
      (∫ z in originalCenteredPhysicalCubeRegion b (2*R), (A.sourceDensity s t z-A.targetDensity s t z)*φ z) =
        originalOrientedStageCurrentInputPairing S w b R ell s t scene φ := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hmη : Measurable η := (contDiff_originalEuclideanMollifier q).continuous.measurable
  filter_upwards [D.ae_originalOrientedOmittedCurrent_C1_divergence_balance hF hw hbounds Q b R ell hst,
    D.ae_all_originalOrientedStagePortDensities_eq_omittedRaw_add_reflectedInput hF hw Q b hell hR hRone s t,
    D.ae_all_originalOrientedStageResidualDensity_meanZero_test_pairing hF hw Q b (by linarith) hR hRone,
    Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 0,
    Q.ae_finite_orientedReflectedInputOuterWindow b (2*R) 1] with scene hcurrent hports hmean hfinS hfinT
  let σ := volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))
  let core := originalOrientedStageResidualCoreDensity S w b R ell s t scene
  let div := fun z ↦ originalStageCurrentDivergence (fun z ↦
    originalOrientedOmittedSeedPathClockSetCurrent S w b R ell (fun x ↦ η (x-z)) (Ioc s t) scene) z
  let src := originalOrientedClassReflectedInputScalarField b η (2*R) (Ico s t) (legalInputColorMeasure q scene.2 0)
  let tgt := originalOrientedClassReflectedInputScalarField b η (2*R) (Ioc s t) (legalInputColorMeasure q scene.2 1)
  have hzs := integrable_originalOrientedClassReflectedInputScalarField_mul (C := Ico s t) b hmη
    (originalEuclideanMollifier_radial q) (originalEuclideanMollifierBound_nonneg q)
    (abs_originalEuclideanMollifier_le q) (originalEuclideanMollifier_unit_range q)
    (show 2 ≤ 2*R by linarith) measurableSet_Ico (legalInputColorMeasure q scene.2 0) hfinS
    (u := fun _ ↦ (1:ℝ)) continuous_const
  have hzt := integrable_originalOrientedClassReflectedInputScalarField_mul (C := Ioc s t) b hmη
    (originalEuclideanMollifier_radial q) (originalEuclideanMollifierBound_nonneg q)
    (abs_originalEuclideanMollifier_le q) (originalEuclideanMollifier_unit_range q)
    (show 2 ≤ 2*R by linarith) measurableSet_Ioc (legalInputColorMeasure q scene.2 1) hfinT
    (u := fun _ ↦ (1:ℝ)) continuous_const
  simp only [mul_one] at hzs hzt
  have he : core =ᵐ[σ] fun z ↦ div z+src z-tgt z := by
    filter_upwards [ae_restrict_mem (isCompact_originalStagePhysicalCube b (2*R)).measurableSet] with z hz
    have hp := hports z hz
    have hd := hcurrent.2 z
    dsimp only [core, originalOrientedStageResidualCoreDensity]
    rw [hp.1, hp.2]
    change div z = _ at hd
    change originalOrientedOmittedCutDensity S w b R ell s scene z +
      (originalOrientedOmittedRawSlabSourceDensity S w b R ell s t z scene + src z) -
      originalOrientedOmittedCutDensity S w b R ell t scene z -
      (originalOrientedOmittedRawSlabTargetDensity S w b R ell s t z scene + tgt z) =
        div z+src z-tgt z
    linarith
  have hd : Integrable div σ := ((hmean.1.sub hzs).add hzt).congr (by
    filter_upwards [he] with z hz
    change core z-src z+tgt z=div z
    linarith)
  intro A hA K φ hφ
  have hmA : (∫ z, φ z ∂A.cubeMeasure) = 0 := hφ
  change (∫ z, (A.sourceDensity s t z-A.targetDensity s t z)*φ z ∂A.cubeMeasure) = _
  rw [hmean.2 A hA K φ hmA]
  change (∫ z, core z*φ z ∂σ) = _
  have hp {f : (Fin q → ℝ) → ℝ} (hf : Integrable f σ) : Integrable (fun z ↦ f z*φ z) σ := by
    simpa only [mul_comm] using smoothTest_mul_density_integrable K σ φ hf
  calc
    _ = ∫ z, div z*φ z+src z*φ z-tgt z*φ z ∂σ := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
      ring
    _ = originalOrientedStageCurrentInputPairing S w b R ell s t scene φ := by
      rw [integral_sub (f := fun z ↦ div z*φ z+src z*φ z) (g := fun z ↦ tgt z*φ z)
        ((hp hd).add (hp hzs)) (hp hzt), integral_add (hp hd) (hp hzs)]
      rfl

/-- One actual scene event controls every same-frame original stage object, every reserve
array and every mean-zero smooth test by the same genuine current/input random coefficient. -/
theorem ae_all_originalOrientedStageResidualDensity_Neumann_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    {s t : ℝ} (hst : s ≤ t)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _)) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell, A.scene = scene →
      ∀ φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ),
      (∫ z in originalCenteredPhysicalCubeRegion b (2*R), φ z) = 0 →
      (∫ z in originalCenteredPhysicalCubeRegion b (2*R), (A.sourceDensity s t z-A.targetDensity s t z)*φ z)^2 ≤
        originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene *
          ‖smoothPhysicalGradientLtwo K (volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))) φ‖^2 := by
  filter_upwards [D.ae_all_originalOrientedStageResidualDensity_currentInput_pairing hF hw hbounds Q b hell hR hst,
    D.ae_originalOrientedStageCurrentInput_Neumann_bound hF hw hq hbounds Q b K hell hR hst hj]
      with scene hread hbound
  intro A hA φ hmean
  rw [hread A hA K φ hmean]
  exact hbound φ hmean

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
