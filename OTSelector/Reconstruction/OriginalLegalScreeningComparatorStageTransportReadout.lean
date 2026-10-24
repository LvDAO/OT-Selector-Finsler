import OTSelector.Reconstruction.OriginalLegalScreeningComparatorStageCountTransport
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorStageLaws

/-! The genuine canonical Neumann producer has the exact background-plus-class
marginals required by the actual ordered transport gluing argument. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff
noncomputable section
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

/-- Actual scene/count/error data generate genuine physical stage plans with
literal background-plus-arrival/departure marginals. The nonnegative actual
cut gammas also produce finite backgrounds. No stage coupling or desired
marginal decomposition is an input. -/
theorem ae_all_originalCanonicalStage_exists_background_class_coupling
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R)
    {s t : ℝ} (hst : s ≤ t) :
    ∃ K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      haarRootCube (Fin (finrank ℝ S.covector.ker)) R ⊆
        interior (K : Set (Fin (finrank ℝ S.covector.ker) → ℝ)) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _),
        A.scene = scene → ∀ r : ℝ, 0 < r → A.goodStageCounts r s t →
        0 ≤ A.gamma s → 0 ≤ A.gamma t →
        IsFiniteMeasure (A.backgroundLaw s) ∧ IsFiniteMeasure (A.backgroundLaw t) ∧
      ∀ ε : ℝ, 0 < ε → ∃ Γ : Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)) ×
          EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        Vlasov.IsCoupling Γ (A.backgroundLaw s+A.sourceArrivalLaw s t)
          (A.backgroundLaw t+A.targetDepartureLaw s t) ∧
        IsFiniteMeasure Γ ∧ Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
        (∫ z, dist z.1 z.2^2 ∂Γ) ≤
          (3*r)⁻¹ * originalCanonicalStageNeumannBudget S w K R ell s t scene + ε := by
  obtain ⟨K, hK, hplans⟩ :=
    D.ae_all_originalCanonicalStageDensities_exists_physical_coupling_on_goodStageCounts
      hF hw hq hbounds Q hell hR hst
  refine ⟨K, hK, ?_⟩
  filter_upwards [hplans,
    D.ae_all_originalCanonicalStageLaws_eq_background_add_class hF hw Q hell hR s t]
      with scene hplans hlaws
  intro A hA r hr hgood hγs hγt
  have hl := hlaws A hA hγs hγt
  refine ⟨hl.1, hl.2.1, ?_⟩
  intro ε hε
  obtain ⟨Γ, hΓ, hfinite, hI, hc⟩ := hplans A hA r hr hgood ε hε
  rw [hl.2.2.1, hl.2.2.2] at hΓ
  exact ⟨Γ, hΓ, hfinite, hI, hc⟩
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
