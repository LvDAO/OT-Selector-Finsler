import OTSelector.Reconstruction.OriginalStageResidualDensityCanonical

/-! Literal stage reserve count slack gives the actual density floor at both
interior and endpoint stages, using the actual full-cut discrepancy. -/
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
namespace OriginalStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {R ell : ℝ}
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}

/-- Actual reserve count available across the stage: source prefix plus its true
half-open class. The same count is target prefix plus its true target class. -/
def reserveStageSlack (A : OriginalStageResidualDensityData S w R ell η) (s t : ℝ) : ℝ :=
  A.reservePrefix s + originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t)

/-- The actual count and full-main cut-error conditions for one true stage. -/
def goodStageCounts (A : OriginalStageResidualDensityData S w R ell η) (r s t : ℝ) : Prop :=
  4*r*A.cubeVolume ≤ A.reserveStageSlack s t ∧
  |originalStageFullCutError S w R s η A.scene| ≤ r*A.cubeVolume ∧
  |originalStageFullCutError S w R t η A.scene| ≤ r*A.cubeVolume

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The two true half-open reserve conventions give exactly the same stage slack. -/
theorem reserveStageSlack_eq_target (A : OriginalStageResidualDensityData S w R ell η)
    {s t : ℝ} (hst : s ≤ t) :
    A.reserveStageSlack s t = A.reservePrefix t +
      originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) := by
  have h := originalStageRemainingReservePrefix_increment A.sourceReserve A.targetReserve
    A.sourceKept A.targetKept hst
  change A.reservePrefix t - A.reservePrefix s = _ at h
  unfold reserveStageSlack
  linarith
end OriginalStageResidualDensityData
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On the actual count-slack event the two original densities have floor 3r.
No incoming/outgoing gamma floor is required; the same formula includes the
first source and last target class when their actual endpoint cut error is zero. -/
theorem ae_all_originalCanonicalStageDensities_floor_on_goodStageCounts
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _),
      A.scene = scene → ∀ r : ℝ, A.goodStageCounts r s t → ∀ z,
        3*r ≤ A.sourceDensity s t z ∧ 3*r ≤ A.targetDensity s t z := by
  let q := finrank ℝ S.covector.ker
  have hη := (contDiff_originalEuclideanMollifier q).continuous
  have hcη := hasCompactSupport_originalEuclideanMollifier q
  have hηI := integrable_originalEuclideanMollifier q
  have hηone := integral_originalEuclideanMollifier_eq_one q
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have heven := coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)
  have hηM := abs_originalEuclideanMollifier_le q
  filter_upwards [D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR s
      hη hcη hηI hηone hsupport heven hηM,
    D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR t
      hη hcη hηI hηone hsupport heven hηM] with scene hs ht
  intro A hA r hgood z
  have hAe : (⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩ :
      OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q)) = A := by
    cases A
    cases hA
    rfl
  have hgs := hs A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  have hgt := ht A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  change (⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩ :
    OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q)).gamma s = _ at hgs
  change (⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩ :
    OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q)).gamma t = _ at hgt
  rw [hAe] at hgs hgt
  rw [← hA] at hgs hgt
  have hV := A.cubeVolume_pos (by linarith)
  have hsource : 3*r ≤ A.gamma s +
      (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ)/A.cubeVolume := by
    rw [hgs, ← add_div]
    apply (le_div_iff₀ hV).mpr
    have hl := (abs_le.mp hgood.2.1).1
    have hcount : 4*r*A.cubeVolume ≤ A.reservePrefix s +
        originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) := hgood.1
    linarith [hcount]
  have htarget : 3*r ≤ A.gamma t +
      (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ)/A.cubeVolume := by
    rw [hgt, ← add_div]
    apply (le_div_iff₀ hV).mpr
    have hl := (abs_le.mp hgood.2.2).1
    have hslack := A.reserveStageSlack_eq_target hst
    linarith [hgood.1]
  have hηnonneg := originalEuclideanMollifier_nonneg q
  have hνs := originalOmittedCutDensity_nonneg S w R ell s hηnonneg z A.scene
  have hνt := originalOmittedCutDensity_nonneg S w R ell t hηnonneg z A.scene
  have hps : 0 ≤ originalStageSourcePortDensity S w R ell (originalEuclideanMollifier q)
      (Ico s t) A.scene z := originalStageReflectedClassDensity_nonneg hηnonneg R _ _ z
  have hpt : 0 ≤ originalStageTargetPortDensity S w R ell (originalEuclideanMollifier q)
      (Ioc s t) A.scene z := originalStageReflectedClassDensity_nonneg hηnonneg R _ _ z
  unfold OriginalStageResidualDensityData.sourceDensity OriginalStageResidualDensityData.targetDensity
  constructor <;> linarith
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
