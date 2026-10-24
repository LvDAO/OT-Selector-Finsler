import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedGammaCancellation

/-! Literal actual count/error events give the same-frame stage density floor. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalOrientedStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
  (A : OriginalOrientedStageResidualDensityData S w b R ell)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The same actual oriented volume equals its exact physical cube volume. -/
theorem cubeVolume_eq (hR : 0 ≤ R) : A.cubeVolume = (2 * R) ^ (finrank ℝ S.covector.ker) := by
  have hcube : originalCenteredPhysicalCubeRegion b (2 * R) =
      (orthonormalPhysicalCubeMap b).symm ⁻¹' haarRootCube (Fin (finrank ℝ S.covector.ker)) R := by
    ext z
    simpa only [Set.mem_preimage, show 2 * R / 2 = R by ring] using
      mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) z
  have hvol : volume (originalCenteredPhysicalCubeRegion b (2 * R)) =
      volume (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) := by
    rw [hcube]
    exact (measurePreserving_orthonormalPhysicalCubeMap_symm b).measure_preimage measurableSet_Icc.nullMeasurableSet
  unfold cubeVolume cubeMeasure
  rw [measureReal_def, Measure.restrict_apply_univ, hvol]
  simpa only [Fintype.card_fin, measureReal_def] using
    volume_real_haarRootCube (Fin (finrank ℝ S.covector.ker)) hR

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem cubeVolume_pos (hR : 0 < R) : 0 < A.cubeVolume := by
  rw [A.cubeVolume_eq hR.le]
  positivity

/-- An actual good cut is a literal remaining-reserve count inequality and a literal
full-main cut-error inequality; gamma and density conclusions are not part of the event. -/
def goodCut (r c : ℝ) : Prop :=
  4 * r * A.cubeVolume ≤ A.reservePrefix c ∧
    |originalOrientedStageFullCutError S w b R c A.scene| ≤ r * A.cubeVolume

end OriginalOrientedStageResidualDensityData
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual count slack and the actual full-main error bound imply the paper's positive
gamma and density floors for the same original oriented stage data. -/
theorem ae_all_originalOrientedStageGoodCuts_floor
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell s t : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalOrientedStageResidualDensityData S w b R ell :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      ∀ r : ℝ, A.goodCut r s → A.goodCut r t →
        3 * r ≤ A.gamma s ∧ 3 * r ≤ A.gamma t ∧
          ∀ z, 3 * r ≤ A.sourceDensity s t z ∧ 3 * r ≤ A.targetDensity s t z := by
  filter_upwards [D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone s,
    D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone t]
    with scene hs ht
  intro sourceReserve targetReserve sourceKept targetKept
  dsimp only
  let A : OriginalOrientedStageResidualDensityData S w b R ell :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  intro r hgs hgt
  have hV := A.cubeVolume_pos (by linarith : 0 < R)
  have hfloor (c : ℝ) (hg : A.goodCut r c)
      (hc : A.gamma c = (A.reservePrefix c + originalOrientedStageFullCutError S w b R c scene) / A.cubeVolume) :
      3 * r ≤ A.gamma c := by
    rw [hc]
    apply (le_div_iff₀ hV).mpr
    have hδ := (abs_le.mp hg.2).1
    linarith [hg.1]
  have hfs := hfloor s hgs (hs sourceReserve targetReserve sourceKept targetKept)
  have hft := hfloor t hgt (ht sourceReserve targetReserve sourceKept targetKept)
  refine ⟨hfs, hft, fun z ↦ ?_⟩
  have hνs := originalOrientedOmittedCutDensity_nonneg S w b R ell s scene z
  have hνt := originalOrientedOmittedCutDensity_nonneg S w b R ell t scene z
  have hps := originalOrientedStageReflectedClassDensity_nonneg b R (Ico s t) A.sourcePortMeasure z
  have hpt := originalOrientedStageReflectedClassDensity_nonneg b R (Ioc s t) A.targetPortMeasure z
  have hcs : 0 ≤ (originalStageRemainingReserveClassCount sourceReserve sourceKept (Ico s t) : ℝ) / A.cubeVolume :=
    div_nonneg (Nat.cast_nonneg _) hV.le
  have hct : 0 ≤ (originalStageRemainingReserveClassCount targetReserve targetKept (Ioc s t) : ℝ) / A.cubeVolume :=
    div_nonneg (Nat.cast_nonneg _) hV.le
  constructor <;> dsimp only [OriginalOrientedStageResidualDensityData.sourceDensity,
    OriginalOrientedStageResidualDensityData.targetDensity, A] at * <;> linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
