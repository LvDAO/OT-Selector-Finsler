import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedData

/-! Actual same-frame stage densities are integrable and have equal mass. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Centering by the literal own integral leaves the actual prefix and arrival mass.
This algebraic readout is shared by both actual oriented stage colours. -/
theorem integral_originalStageCenteredDensity {q : ℕ}
    (σ : Measure (Fin q → ℝ)) [IsFiniteMeasure σ] {ν a : (Fin q → ℝ) → ℝ}
    (hν : Integrable ν σ) (ha : Integrable a σ) {P H h : ℝ} (hV : σ.real univ ≠ 0) :
    (∫ z, ν z + (P + H - ∫ x, ν x ∂σ) / σ.real univ + a z + h / σ.real univ ∂σ) =
      P + H + (∫ z, a z ∂σ) + h := by
  rw [integral_add (f := fun z ↦ ν z + (P + H - ∫ x, ν x ∂σ) / σ.real univ + a z)
      (g := fun _ ↦ h / σ.real univ) ((hν.add (integrable_const _)).add ha) (integrable_const _),
    integral_add (f := fun z ↦ ν z + (P + H - ∫ x, ν x ∂σ) / σ.real univ) (g := a)
      (hν.add (integrable_const _)) ha,
    integral_add (f := ν) (g := fun _ ↦ (P + H - ∫ x, ν x ∂σ) / σ.real univ)
      hν (integrable_const _)]
  simp only [integral_const, smul_eq_mul]
  field_simp
  ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- One actual scene event works for all original reserve arrays and all adaptively kept
indices: the literal same-frame stage densities are spatially L1 and have equal mass.
No desired mass equality, count balance, floor, cut cancellation or spatial law is assumed. -/
theorem ae_all_originalOrientedStageDensities_integrable_equal_mass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell s t : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalOrientedStageResidualDensityData S w b R ell :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      Integrable (A.sourceDensity s t) A.cubeMeasure ∧
      Integrable (A.targetDensity s t) A.cubeMeasure ∧
        (∫ z, A.sourceDensity s t z ∂A.cubeMeasure) = ∫ z, A.targetDensity s t z ∂A.cubeMeasure := by
  filter_upwards [D.ae_originalOrientedStagePlans_finite hF hw Q b hell hR,
    D.ae_all_originalOrientedStagePortDensities_integrable_mass hF hw Q b hell hR hRone,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell s,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell t] with scene hfinite hports hνs hνt
  intro sourceReserve targetReserve sourceKept targetKept
  let A : OriginalOrientedStageResidualDensityData S w b R ell :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  let : IsFiniteMeasure A.cubeMeasure := ⟨by
    change (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) univ < (∞ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ]
    exact (isCompact_originalStagePhysicalCube b (2 * R)).measure_lt_top⟩
  let : IsFiniteMeasure (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) :=
    inferInstanceAs (IsFiniteMeasure A.cubeMeasure)
  have hcube : originalCenteredPhysicalCubeRegion b (2 * R) =
      (orthonormalPhysicalCubeMap b).symm ⁻¹' haarRootCube (Fin (finrank ℝ S.covector.ker)) R := by
    ext z
    simpa only [Set.mem_preimage, show 2 * R / 2 = R by ring] using
      mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) z
  have hvol : volume (originalCenteredPhysicalCubeRegion b (2 * R)) =
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) := by
    rw [hcube]
    exact (measurePreserving_orthonormalPhysicalCubeMap_symm b).measure_preimage measurableSet_Icc.nullMeasurableSet
  have hV : A.cubeMeasure.real univ ≠ 0 := by
    change (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))).real univ ≠ 0
    rw [measureReal_def, Measure.restrict_apply_univ, hvol]
    change volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) ≠ 0
    rw [volume_real_haarRootCube _ (by linarith)]
    positivity
  have hs : Integrable (originalOrientedStageReflectedClassDensity b R (Ico s t) A.sourcePortMeasure) A.cubeMeasure ∧
      (∫ z, originalOrientedStageReflectedClassDensity b R (Ico s t) A.sourcePortMeasure z ∂A.cubeMeasure) =
        A.sourcePortMeasure.real {p | p.2 ∈ Ico s t} := (hports (Ico s t)).1
  have ht : Integrable (originalOrientedStageReflectedClassDensity b R (Ioc s t) A.targetPortMeasure) A.cubeMeasure ∧
      (∫ z, originalOrientedStageReflectedClassDensity b R (Ioc s t) A.targetPortMeasure z ∂A.cubeMeasure) =
        A.targetPortMeasure.real {p | p.2 ∈ Ioc s t} := (hports (Ioc s t)).2
  refine ⟨((hνs.add (integrable_const _)).add hs.1).add (integrable_const _),
    ((hνt.add (integrable_const _)).add ht.1).add (integrable_const _), ?_⟩
  have hsm := integral_originalStageCenteredDensity A.cubeMeasure hνs hs.1 (P := A.portPrefix s)
    (H := A.reservePrefix s) (h := (originalStageRemainingReserveClassCount sourceReserve sourceKept (Ico s t) : ℝ)) hV
  have htm := integral_originalStageCenteredDensity A.cubeMeasure hνt ht.1 (P := A.portPrefix t)
    (H := A.reservePrefix t) (h := (originalStageRemainingReserveClassCount targetReserve targetKept (Ioc s t) : ℝ)) hV
  change (∫ z, A.sourceDensity s t z ∂A.cubeMeasure) = _ at hsm
  change (∫ z, A.targetDensity s t z ∂A.cubeMeasure) = _ at htm
  let : IsFiniteMeasure (originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := hfinite.2.1
  let : IsFiniteMeasure (originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
    (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := hfinite.2.2
  let : IsFiniteMeasure A.sourcePortMeasure := ⟨by
    change ((originalStageWindowSourcePortPlan (originalOrientedPathLengthRetained S w b R ell)
      (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map Prod.fst) univ < (∞ : ℝ≥0∞)
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    exact hfinite.2.1.measure_univ_lt_top⟩
  let : IsFiniteMeasure A.targetPortMeasure := ⟨by
    change ((originalStageWindowTargetPortPlan (originalOrientedPathLengthRetained S w b R ell)
      (originalCenteredPhysicalCubeRegion b (2 * R)) scene : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map Prod.snd) univ < (∞ : ℝ≥0∞)
    rw [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ]
    exact hfinite.2.2.measure_univ_lt_top⟩
  have hsp := (originalStageClockMeasure_prefix_increments A.sourcePortMeasure hst).1
  have htp := (originalStageClockMeasure_prefix_increments A.targetPortMeasure hst).2
  have hr := originalStageRemainingReservePrefix_increment sourceReserve targetReserve sourceKept targetKept hst
  rw [hsm, htm, hs.2, ht.2]
  dsimp only [A, OriginalOrientedStageResidualDensityData.portPrefix,
    OriginalOrientedStageResidualDensityData.reservePrefix,
    OriginalOrientedStageResidualDensityData.sourcePortMeasure,
    OriginalOrientedStageResidualDensityData.targetPortMeasure] at hsp htp ⊢
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
