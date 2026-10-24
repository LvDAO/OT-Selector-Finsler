import OTSelector.Reconstruction.OriginalStageResidualDensityActualPorts
import OTSelector.Reconstruction.OriginalStageResidualDensityReserveCounts
import OTSelector.Reconstruction.OriginalStageResidualDensityCutIntegrability

/-! Literal original omitted-cut, port and surviving-reserve stage densities have equal mass. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem integral_stage_density (σ : Measure (Fin q → ℝ)) [IsFiniteMeasure σ]
    {ν a : (Fin q → ℝ) → ℝ} (hν : Integrable ν σ) (ha : Integrable a σ)
    {P H h : ℝ} (hV : σ.real univ ≠ 0) :
    (∫ z, ν z + (P + H - ∫ x, ν x ∂σ) / σ.real univ + a z + h / σ.real univ ∂σ) =
      P + H + (∫ z, a z ∂σ) + h := by
  rw [integral_add (f := fun z ↦ ν z + (P + H - ∫ x, ν x ∂σ) / σ.real univ + a z)
      (g := fun _ ↦ h / σ.real univ)
      ((hν.add (integrable_const _)).add ha) (integrable_const _),
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

/-- One actual original scene and the unchanged original reserve observations and surviving
indices. All path, port, cut, volume and density readouts below are literal functions of these. -/
structure OriginalStageResidualDensityData (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) where
  scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)
  sourceReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ
  targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ
  sourceKept : Finset (Fin sourceReserve.1)
  targetKept : Finset (Fin targetReserve.1)

namespace OriginalStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {R ell : ℝ}
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
  (A : OriginalStageResidualDensityData S w R ell η)

/-- The actual physical Haar volume of the same original cube. -/
def cubeVolume (_A : OriginalStageResidualDensityData S w R ell η) : ℝ := volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)

/-- Signed prefix count of exactly the original source and target port marginals. -/
def portPrefix (c : ℝ) : ℝ :=
  (originalPathSourcePortPlan S w R ell A.scene :
    Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst.real {p | p.2 < c} -
  (originalPathTargetPortPlan S w R ell A.scene :
    Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd.real {p | p.2 ≤ c}

/-- The actual surviving original reserve source-minus-target prefix. -/
def reservePrefix (c : ℝ) : ℝ :=
  originalStageRemainingReservePrefix A.sourceReserve A.targetReserve A.sourceKept A.targetKept c

/-- The literal paper gamma, before proving any separate full-cut error cancellation. -/
def gamma (c : ℝ) : ℝ :=
  (A.portPrefix c + A.reservePrefix c -
    ∫ z in haarRootCube _ R, originalOmittedCutDensity S w R ell c η z A.scene) / A.cubeVolume

/-- Actual stage source density: incoming omitted occupation, constant gamma, source ports
of the true half-open clock slab, and the surviving original source reserve class count. -/
def sourceDensity (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOmittedCutDensity S w R ell s η z A.scene + A.gamma s +
    originalStageSourcePortDensity S w R ell η (Ico s t) A.scene z +
    (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) /
      A.cubeVolume

/-- Actual stage target density uses the same original target ports and surviving target
reserve indices, with the exact outgoing-cut convention. -/
def targetDensity (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  originalOmittedCutDensity S w R ell t η z A.scene + A.gamma t +
    originalStageTargetPortDensity S w R ell η (Ioc s t) A.scene z +
    (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) /
      A.cubeVolume

end OriginalStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual original stage densities are genuinely L1 and have equal total mass.
The gamma definition, true port mass preservation and original reserve prefix counts suffice;
no cut cancellation, class monochromaticity, positive floor or stage equal-mass premise is used. -/
theorem ae_originalStageResidualDensities_integrable_equal_mass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) (hRone : 1 ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M)
    (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
    (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1))
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A : OriginalStageResidualDensityData S w R ell η :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      Integrable (A.sourceDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      Integrable (A.targetDensity s t) (volume.restrict (haarRootCube _ R)) ∧
      (∫ z in haarRootCube _ R, A.sourceDensity s t z) =
        ∫ z in haarRootCube _ R, A.targetDensity s t z := by
  filter_upwards [D.ae_originalStagePortMeasures_finite hF hw Q hell hR,
    D.ae_all_originalStagePortDensities_integrable_mass hF hw Q hell hR hRone
      hη hηI hηone hηsupport hηeven hηM,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (R := R) (by linarith) ell s hη hηM hηsupport,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q (R := R) (by linarith) ell t hη hηM hηsupport]
    with scene hfinite hports hνs hνt
  let A : OriginalStageResidualDensityData S w R ell η :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  let σ := volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)
  have : IsFiniteMeasure σ := ⟨by
    change (volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) univ < (∞ : ℝ≥0∞)
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hvolume : σ.real univ = A.cubeVolume := by simp [σ, OriginalStageResidualDensityData.cubeVolume,
    measureReal_def]
  have hV : σ.real univ ≠ 0 := by
    rw [hvolume, OriginalStageResidualDensityData.cubeVolume, volume_real_haarRootCube _ (by linarith)]
    positivity
  have hsource := (hports (Ico s t)).1
  have htarget := (hports (Ioc s t)).2
  refine ⟨((hνs.add (integrable_const _)).add hsource.1).add (integrable_const _),
    ((hνt.add (integrable_const _)).add htarget.1).add (integrable_const _), ?_⟩
  change (∫ z, A.sourceDensity s t z ∂σ) = ∫ z, A.targetDensity s t z ∂σ
  have hsourceMass := integral_stage_density σ hνs hsource.1 (P := A.portPrefix s)
    (H := A.reservePrefix s)
    (h := (originalStageRemainingReserveClassCount sourceReserve sourceKept (Ico s t) : ℝ)) hV
  have htargetMass := integral_stage_density σ hνt htarget.1 (P := A.portPrefix t)
    (H := A.reservePrefix t)
    (h := (originalStageRemainingReserveClassCount targetReserve targetKept (Ioc s t) : ℝ)) hV
  rw [hvolume] at hsourceMass htargetMass
  change (∫ z, A.sourceDensity s t z ∂σ) = _ at hsourceMass
  change (∫ z, A.targetDensity s t z ∂σ) = _ at htargetMass
  have : IsFiniteMeasure (originalPathSourcePortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst := hfinite.1
  have : IsFiniteMeasure (originalPathTargetPortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd := hfinite.2
  have hs := (originalStageClockMeasure_prefix_increments
    (originalPathSourcePortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst hst).1
  have ht := (originalStageClockMeasure_prefix_increments
    (originalPathTargetPortPlan S w R ell scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd hst).2
  have hr := originalStageRemainingReservePrefix_increment sourceReserve targetReserve
    sourceKept targetKept hst
  rw [hsourceMass, htargetMass, hsource.2, htarget.2]
  dsimp [A, OriginalStageResidualDensityData.portPrefix,
    OriginalStageResidualDensityData.reservePrefix]
  linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
