import OTSelector.Reconstruction.OriginalStageResidualDensityExcessEndpoints
import OTSelector.Reconstruction.OriginalStageResidualDensityExcessMarksOnly
import OTSelector.Probability.MarkedCloudCarriers

/-! The original independent Poisson reserve marks supply endpoint gamma without support callbacks. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal NNReal Topology ContDiff BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- One event under the actual two independent original Poisson reserve clouds places every
original mark, hence every adaptively kept finite index, in its original open clock support. -/
theorem ae_all_originalReserveCloud_interior_clocks (rate : ℝ≥0) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ᵐ reserves ∂twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate,
      (∀ i : ℕ, D.lo + (S.level : ℝ) < (reserves.1.2 i).2 ∧
        (reserves.1.2 i).2 < D.hi + (S.level : ℝ)) ∧
      (∀ i : ℕ, D.lo + (S.level : ℝ) < (reserves.2.2 i).2 ∧
        (reserves.2.2 i).2 < D.hi + (S.level : ℝ)) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  have hp : ∀ᵐ p ∂μ.prod ν,
      p.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ p.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    (ae_fst_of_ae D.support.source.ae_open).and (ae_snd_of_ae D.support.target.ae_open)
  filter_upwards [ae_all_mMarkPair (finrank ℝ S.covector.ker) μ ν rate
    (P := fun a b ↦ a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b - (S.level : ℝ) ∈ Ioo D.lo D.hi) hp] with reserves hres
  constructor
  · intro i
    have h := (hres i 0).1
    change (reserves.1.2 i).2 - (S.level : ℝ) ∈ Ioo D.lo D.hi at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro i
    have h := (hres 0 i).2
    change (reserves.2.2 i).2 - (S.level : ℝ) ∈ Ioo D.lo D.hi at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The actual full-scene law and independent original reserve clouds jointly produce main
window arrays and both endpoint gamma equalities after genuine excess removal. Only actual
extreme-class capacity remains, and it is produced by countGood_removal_protection. Spatial
replacement preserves selection, so this event also applies to every physical placement of
the same original reserve marks and indices. -/
theorem ae_originalFullScene_reserveLaw_endpoint_gamma_eq_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) (rate : ℝ≥0) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ᵐ p ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).prod
        (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate),
      (∃ sourceMain targetMain, IsOriginalStageMainWindowArrays R p.1 sourceMain targetMain) ∧
      ∀ (sourceMain targetMain : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (firstClass lastClass : Set ℝ)
        (sourcePositions targetPositions : ℕ → (Fin (finrank ℝ S.covector.ker) → ℝ)),
      IsOriginalStageMainWindowArrays R p.1 sourceMain targetMain →
      let A : OriginalStageExcessRemovalData (finrank ℝ S.covector.ker) :=
        ⟨sourceMain, targetMain,
          originalStageReplaceCloudPositions p.2.1 sourcePositions,
          originalStageReplaceCloudPositions p.2.2 targetPositions, firstClass, lastClass⟩
      A.hasCapacity →
      let B : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _) :=
        ⟨p.1, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩
      B.gamma (D.lo + (S.level : ℝ)) = 0 ∧ B.gamma (D.hi + (S.level : ℝ)) = 0 := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  filter_upwards [ae_fst_of_ae (Q.ae_exists_originalStageMainWindowArrays R),
    ae_fst_of_ae (D.ae_all_originalStageExcessRemoval_endpoint_gamma_eq_zero hF hw Q hell hR),
    ae_snd_of_ae (D.ae_all_originalReserveCloud_interior_clocks rate)] with p harray hgamma hmarks
  refine ⟨harray, ?_⟩
  intro sourceMain targetMain firstClass lastClass sourcePositions targetPositions hrep
  dsimp only
  intro hcap
  exact hgamma ⟨sourceMain, targetMain,
      originalStageReplaceCloudPositions p.2.1 sourcePositions,
      originalStageReplaceCloudPositions p.2.2 targetPositions, firstClass, lastClass⟩ hrep
    (fun i ↦ hmarks.1 i) (fun i ↦ hmarks.2 i) hcap

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
