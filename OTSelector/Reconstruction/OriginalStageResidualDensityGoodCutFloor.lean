import OTSelector.Reconstruction.OriginalStageResidualDensityGammaCancellation

/-! The paper's actual reserve-count and full-cut-error event produces the stage floor. -/
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
  (A : OriginalStageResidualDensityData S w R ell η)

/-- Literal reserve-prefix count slack and the actual full-main delta bound at this cut.
This is an event on the actual counts and measures, with no gamma or density-floor clause. -/
def goodCut (r c : ℝ) : Prop :=
  4 * r * A.cubeVolume ≤ A.reservePrefix c ∧
    |originalStageFullCutError S w R c η A.scene| ≤ r * A.cubeVolume

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual physical cube volume is positive. -/
theorem cubeVolume_pos (hR : 0 < R) : 0 < A.cubeVolume := by
  rw [cubeVolume, volume_real_haarRootCube _ hR.le]
  positivity

omit [BorelSpace E] in
/-- Nonnegative omitted occupation, genuine reflected ports and actual reserve counts
make the source density at least its incoming gamma. -/
theorem gamma_le_sourceDensity (hR : 0 < R) (hη : ∀ x, 0 ≤ η x)
    (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    A.gamma s ≤ A.sourceDensity s t z := by
  have hn := originalOmittedCutDensity_nonneg S w R ell s hη z A.scene
  have hp : 0 ≤ originalStageSourcePortDensity S w R ell η (Ico s t) A.scene z :=
    originalStageReflectedClassDensity_nonneg hη R _ _ z
  have hc : 0 ≤ (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept
      (Ico s t) : ℝ) / A.cubeVolume := div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hR).le
  unfold sourceDensity
  linarith

omit [BorelSpace E] in
/-- The actual target density is at least its outgoing gamma, with the same original data. -/
theorem gamma_le_targetDensity (hR : 0 < R) (hη : ∀ x, 0 ≤ η x)
    (s t : ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) :
    A.gamma t ≤ A.targetDensity s t z := by
  have hn := originalOmittedCutDensity_nonneg S w R ell t hη z A.scene
  have hp : 0 ≤ originalStageTargetPortDensity S w R ell η (Ioc s t) A.scene z :=
    originalStageReflectedClassDensity_nonneg hη R _ _ z
  have hc : 0 ≤ (originalStageRemainingReserveClassCount A.targetReserve A.targetKept
      (Ioc s t) : ℝ) / A.cubeVolume := div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hR).le
  unfold targetDensity
  linarith

end OriginalStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual reserve prefix >= 4rV and actual full-main |delta| <= rV imply gamma >= 3r.
The full-cut cancellation is produced from the same original matching, not assumed. -/
theorem ae_all_originalStageGamma_floor_on_goodCut
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) (c : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hηI : Integrable η volume)
    (hηone : ∫ x, η x = 1) (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell η :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      ∀ r : ℝ, A.goodCut r c → 3 * r ≤ A.gamma c := by
  filter_upwards [D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q
    hell hR c hη hcη hηI hηone hηsupport hηeven hηM] with scene hgamma
  intro sourceReserve targetReserve sourceKept targetKept
  dsimp only
  intro r hgood
  let A : OriginalStageResidualDensityData S w R ell η :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  have hg : A.gamma c = (A.reservePrefix c + originalStageFullCutError S w R c η scene) /
      A.cubeVolume := hgamma sourceReserve targetReserve sourceKept targetKept
  rw [hg]
  apply (le_div_iff₀ (A.cubeVolume_pos (by linarith))).mpr
  have hlower := (abs_le.mp hgood.2).1
  linarith [hgood.1]

/-- At an interior stage both literal densities have the required 3r pointwise floor on
the actual two adjacent count/delta events. No desired density-floor premise is supplied. -/
theorem ae_all_originalStageDensities_floor_on_goodCuts
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) (s t : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Continuous η) (hcη : HasCompactSupport η) (hηI : Integrable η volume)
    (hηnonneg : ∀ x, 0 ≤ η x) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (sourceReserve targetReserve : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1)),
      let A : OriginalStageResidualDensityData S w R ell η :=
        ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
      ∀ r : ℝ, A.goodCut r s → A.goodCut r t → ∀ z,
        3 * r ≤ A.sourceDensity s t z ∧ 3 * r ≤ A.targetDensity s t z := by
  filter_upwards [D.ae_all_originalStageGamma_floor_on_goodCut hF hw Q hell hR s hη hcη
      hηI hηone hηsupport hηeven hηM,
    D.ae_all_originalStageGamma_floor_on_goodCut hF hw Q hell hR t hη hcη hηI hηone
      hηsupport hηeven hηM] with scene hs ht
  intro sourceReserve targetReserve sourceKept targetKept
  dsimp only
  intro r hgs hgt z
  let A : OriginalStageResidualDensityData S w R ell η :=
    ⟨scene, sourceReserve, targetReserve, sourceKept, targetKept⟩
  exact ⟨(hs sourceReserve targetReserve sourceKept targetKept r hgs).trans
      (A.gamma_le_sourceDensity (by linarith) hηnonneg s t z),
    (ht sourceReserve targetReserve sourceKept targetKept r hgt).trans
      (A.gamma_le_targetDensity (by linarith) hηnonneg s t z)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
