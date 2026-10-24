import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannCutoff
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannTransport
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorPhysicalTransport
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorStageCountEvent
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetCanonical
import OTSelector.Reconstruction.OriginalStageResidualDensityUniformReserves

/-! The actual count slack, full-cut errors and same-scene Neumann energy
construct real physical stage plans, including nonempty first and last stages. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
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

/-- The same actual count/error conditions generate finite physical Euclidean
stage couplings for every original reserve choice on one original-scene event.
The test compact, cutoff, all-test estimate and actual stage plan are all produced
internally. The only cost budget is the literal same-scene Neumann energy. -/
theorem ae_all_originalCanonicalStageDensities_exists_physical_coupling_on_goodStageCounts
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
      ∀ ε : ℝ, 0 < ε → ∃ Γ : Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)) ×
          EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        Vlasov.IsCoupling Γ
          (((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (A.sourceDensity s t z))).map (EuclideanSpace.equiv _ ℝ).symm)
          (((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (A.targetDensity s t z))).map (EuclideanSpace.equiv _ ℝ).symm) ∧
        IsFiniteMeasure Γ ∧ Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
        (∫ z, dist z.1 z.2^2 ∂Γ) ≤
          (3*r)⁻¹ * originalCanonicalStageNeumannBudget S w K R ell s t scene + ε := by
  obtain ⟨K, χ, hK, hχ⟩ := exists_originalNeumannTestCutoff
    (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) isCompact_Icc
  refine ⟨K, hK, ?_⟩
  let q := finrank ℝ S.covector.ker
  let σ := volume.restrict (haarRootCube (Fin q) R)
  have hRpos : 0 < R := by linarith
  have : IsFiniteMeasure σ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact isCompact_Icc.measure_lt_top⟩
  have hσpos : 0 < σ.real univ := by
    change 0 < (volume.restrict (haarRootCube (Fin q) R)).real univ
    rw [measureReal_def, Measure.restrict_apply_univ]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube _ hRpos.le]
    positivity
  have hσ : ∀ᵐ z ∂σ, z ∈ haarRootCube (Fin q) R := ae_restrict_mem measurableSet_Icc
  filter_upwards [D.ae_all_originalCanonicalStageDensities_integrable_equal_mass_uniform_reserves
      hF hw Q hell hR hst,
    D.ae_all_originalCanonicalStageResidualDensity_Neumann_bound hF hw hq hbounds Q hell hR hst K,
    D.ae_all_originalCanonicalStageDensities_floor_on_goodStageCounts hF hw Q hell hR hst]
      with scene hmass hbudget hfloor
  intro A hA r hr hgood ε hε
  have hAe : (⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩ :
      OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q)) = A := by
    cases A
    cases hA
    rfl
  have hm := hmass A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  dsimp only at hm
  rw [hAe] at hm
  have hl := hfloor A hA r hgood
  have hbound : ∀ ψ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z, ψ z ∂σ) = 0 →
      |∫ z, ψ z * (A.sourceDensity s t z-A.targetDensity s t z) ∂σ|^2 ≤
        originalCanonicalStageNeumannBudget S w K R ell s t scene *
          ‖smoothPhysicalGradientLtwo K σ ψ‖^2 := by
    intro ψ hψ
    simpa only [mul_comm, sq_abs] using hbudget A hA ψ hψ
  obtain ⟨π, hπ, hfinite, hI, hc⟩ :=
    exists_originalDensity_quadratic_coupling_of_meanZero_squared_bound K σ
      isCompact_Icc hK χ hσ hχ hσpos (A.sourceDensity s t) (A.targetDensity s t)
      hm.1 hm.2.1 (by positivity : 0 < 3*r)
      (originalCanonicalStageNeumannBudget_nonneg S w K hRpos.le ell s t scene)
      (Filter.Eventually.of_forall (fun z ↦ (hl z).1))
      (Filter.Eventually.of_forall (fun z ↦ (hl z).2)) hm.2.2 hbound ε hε
  have hphysical := originalRawQuadraticCoupling_toEuclidean _ _ π hπ hI
  exact ⟨_, hphysical.1, hphysical.2.1, hphysical.2.2.1, hphysical.2.2.2.trans_le hc⟩
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
