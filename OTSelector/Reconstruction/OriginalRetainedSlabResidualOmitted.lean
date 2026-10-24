import OTSelector.Reconstruction.OriginalRetainedSlabResidualWeakBalance

/-! Genuine positive omitted cuts and the exact full-current minus retained-current slab. -/
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

/-- Positive occupation at the true clock cut of every original path omitted by retention.
Neither its source nor its target is required to lie in the spatial cube. -/
def originalOmittedSceneActiveCutMeasure (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalRestrictedSceneActiveCutMeasure S w (originalPathLengthRetained S w R ell)ᶜ c scene

/-- The actual omitted source charge, including its positive incoming physical cut. -/
def originalOmittedSceneSlabResidualSource (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalRestrictedSceneSlabSourceMeasure (originalPathLengthRetained S w R ell)ᶜ s t scene +
    originalOmittedSceneActiveCutMeasure S w R ell s scene

/-- The actual omitted target charge, including its positive outgoing physical cut. -/
def originalOmittedSceneSlabResidualTarget (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  originalRestrictedSceneSlabTargetMeasure (originalPathLengthRetained S w R ell)ᶜ s t scene +
    originalOmittedSceneActiveCutMeasure S w R ell t scene

/-- The literal raw smoothing of the genuine positive omitted-cut occupation measure. -/
def originalOmittedCutDensity (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (R ell c : ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ x, η (x - z) ∂originalOmittedSceneActiveCutMeasure S w R ell c scene

omit [BorelSpace E] in
/-- A nonnegative smoothing kernel produces a nonnegative actual omitted-cut density. -/
theorem originalOmittedCutDensity_nonneg (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell c : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : ∀ x, 0 ≤ η x)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    0 ≤ originalOmittedCutDensity S w R ell c η z scene :=
  integral_nonneg (fun x ↦ hη (x - z))

/-- The full original positive cut is exactly its retained part plus its genuine omitted part. -/
theorem originalSceneActiveCut_eq_retained_add_omitted
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell c : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    originalSceneActiveCutMeasure S w c scene =
      originalRestrictedSceneActiveCutMeasure S w (originalPathLengthRetained S w R ell) c scene +
      originalOmittedSceneActiveCutMeasure S w R ell c scene := by
  exact (originalRestrictedSceneMarkedPositionMeasure_add_compl
    (measurableSet_originalPathLengthRetained S hF hw R ell)
    (measurable_originalSeedPathOffset S hF hw c) _ scene).symm

/-- Campbell local finiteness of the original charges controls both genuine omitted residuals. -/
theorem ae_originalOmittedSlabResiduals_finiteOnCompacts
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasureOnCompacts (originalOmittedSceneSlabResidualSource S w R ell s t scene) ∧
      IsFiniteMeasureOnCompacts (originalOmittedSceneSlabResidualTarget S w R ell s t scene) := by
  filter_upwards [ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q
    (originalPathLengthRetained S w R ell)ᶜ s t] with scene hscene
  constructor
  · refine ⟨fun {K} hK ↦ ?_⟩
    change (originalRestrictedSceneSlabSourceMeasure _ _ _ scene +
      originalRestrictedSceneActiveCutMeasure S w _ _ scene) K < _
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨hscene.1.lt_top_of_isCompact hK, hscene.2.2.1.lt_top_of_isCompact hK⟩
  · refine ⟨fun {K} hK ↦ ?_⟩
    change (originalRestrictedSceneSlabTargetMeasure _ _ _ scene +
      originalRestrictedSceneActiveCutMeasure S w _ _ scene) K < _
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2
      ⟨hscene.2.1.lt_top_of_isCompact hK, hscene.2.2.2.lt_top_of_isCompact hK⟩

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The full original weak slab minus the same length-retained slab has exactly the two
positive omitted residual measures. Exterior endpoint paths retain their genuine cut occupation. -/
theorem ae_all_originalWeakSlab_sub_retained_eq_omittedResidualMeasures
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell : ℝ) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 φ → HasCompactSupport φ →
        -(originalSeedPathWeakSlabReadout S w φ s t scene -
          originalRestrictedSeedPathWeakSlabReadout S w
            (originalPathLengthRetained S w R ell) φ s t scene) =
          (∫ x, φ x ∂originalOmittedSceneSlabResidualSource S w R ell s t scene) -
          (∫ x, φ x ∂originalOmittedSceneSlabResidualTarget S w R ell s t scene) := by
  filter_upwards [ae_originalRestrictedSceneSlabCharges_finiteOnCompacts S hF hw Q
      (originalPathLengthRetained S w R ell)ᶜ s t,
    D.ae_all_originalWeakSlab_sub_restricted_positive_balance hF hw Q
      (measurableSet_originalPathLengthRetained S hF hw R ell) hst]
    with scene hfinite hbalance
  intro φ hφ hcφ
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabSourceMeasure
      (originalPathLengthRetained S w R ell)ᶜ s t scene) := hfinite.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneSlabTargetMeasure
      (originalPathLengthRetained S w R ell)ᶜ s t scene) := hfinite.2.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w
      (originalPathLengthRetained S w R ell)ᶜ s scene) := hfinite.2.2.1
  have : IsFiniteMeasureOnCompacts (originalRestrictedSceneActiveCutMeasure S w
      (originalPathLengthRetained S w R ell)ᶜ t scene) := hfinite.2.2.2
  have hsrc : Integrable φ (originalRestrictedSceneSlabSourceMeasure
      (originalPathLengthRetained S w R ell)ᶜ s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have htgt : Integrable φ (originalRestrictedSceneSlabTargetMeasure
      (originalPathLengthRetained S w R ell)ᶜ s t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcuts : Integrable φ (originalRestrictedSceneActiveCutMeasure S w
      (originalPathLengthRetained S w R ell)ᶜ s scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hcutt : Integrable φ (originalRestrictedSceneActiveCutMeasure S w
      (originalPathLengthRetained S w R ell)ᶜ t scene) :=
    hφ.continuous.integrable_of_hasCompactSupport hcφ
  rw [originalOmittedSceneSlabResidualSource, originalOmittedSceneSlabResidualTarget,
    originalOmittedSceneActiveCutMeasure, originalOmittedSceneActiveCutMeasure,
    integral_add_measure hsrc hcuts, integral_add_measure htgt hcutt]
  linarith [(hbalance φ hφ hcφ).2]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
