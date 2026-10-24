import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsLaws
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedStageTransport

/-! Genuine same-frame stage plans have the actual background-plus-arrival marginals. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}

namespace OriginalSeedConditionalMoments
variable {μ ν : Measure ℝ} (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The genuine Neumann plan has exact same-frame background-plus-port/reserve class
marginals, with local scalar floors and its actual physical quadratic budget. -/
theorem ae_all_originalOrientedStageBackground_exists_quadratic_coupling
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    {s t : ℝ} (hst : s ≤ t)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc s t) scene k) 2 (Q.law : Measure _)) :
    ∃ K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      originalCenteredPhysicalCubeRegion b (2*R) ⊆ interior (K : Set _) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell, A.scene = scene →
      0 ≤ A.gamma s → 0 ≤ A.gamma t →
      IsFiniteMeasure (A.orientedBackgroundLaw s) ∧ IsFiniteMeasure (A.orientedBackgroundLaw t) ∧
      ∀ ρ : ℝ, 0 < ρ →
        ρ ≤ A.gamma s +
          (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume →
        ρ ≤ A.gamma t +
          (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume →
      ∀ ε : ℝ, 0 < ε →
      ∃ Γ : Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)) ×
          EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        IsFiniteMeasure Γ ∧
        Γ.fst = A.orientedBackgroundLaw s + A.orientedSourceArrivalLaw s t ∧
        Γ.snd = A.orientedBackgroundLaw t + A.orientedTargetDepartureLaw s t ∧
        Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
        (∫ z, dist z.1 z.2^2 ∂Γ) ≤
          ρ⁻¹ * originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene + ε := by
  obtain ⟨K,hK,hplans⟩ := D.ae_all_originalOrientedStageDensities_exists_quadratic_coupling
    hF hw hq hbounds Q b hell hR hst hj
  refine ⟨K,hK,?_⟩
  filter_upwards [hplans,D.ae_all_originalOrientedStageLaws_eq_background_add_class hF hw Q b hell hR s t]
    with scene hplans hlaws
  intro A hA hgs hgt
  have hl := hlaws A hA hgs hgt
  refine ⟨hl.1,hl.2.1,?_⟩
  intro ρ hρ hs ht ε hε
  obtain ⟨Γ,hΓ,hfin,hI,hcost⟩ := hplans A hA ρ hρ hs ht ε hε
  exact ⟨Γ,hfin,hΓ.1.trans hl.2.2.1,hΓ.2.trans hl.2.2.2,hI,hcost⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
