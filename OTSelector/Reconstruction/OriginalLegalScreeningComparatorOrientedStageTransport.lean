import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannCutoff
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannTransport
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorPhysicalTransport
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedCanonical
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetOrientedMean
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedEqualMass
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedGoodCut

/-! Actual same-frame stage densities produce finite physical Euclidean transport,
using only the local scalar floor of that individual stage. -/
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

namespace OriginalOrientedStageResidualDensityData
omit [BorelSpace E] in
/-- The actual omitted and reflected terms are nonnegative. Hence a stage's literal
scalar coefficient alone supplies its pointwise floor, including endpoint stages whose
positive floor comes from their own class arrival count. -/
theorem densities_floor_of_local_scalar
    {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell s t ρ : ℝ}
    (A : OriginalOrientedStageResidualDensityData S w b R ell)
    (hs : ρ ≤ A.gamma s +
      (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume)
    (ht : ρ ≤ A.gamma t +
      (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume) :
    ∀ z, ρ ≤ A.sourceDensity s t z ∧ ρ ≤ A.targetDensity s t z := by
  intro z
  have hνs := originalOrientedOmittedCutDensity_nonneg S w b R ell s A.scene z
  have hνt := originalOrientedOmittedCutDensity_nonneg S w b R ell t A.scene z
  have hps := originalOrientedStageReflectedClassDensity_nonneg b R (Ico s t) A.sourcePortMeasure z
  have hpt := originalOrientedStageReflectedClassDensity_nonneg b R (Ioc s t) A.targetPortMeasure z
  constructor <;> dsimp only [sourceDensity, targetDensity] <;> linarith
end OriginalOrientedStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {μ ν : Measure ℝ} (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- A compact test carrier is chosen from the actual same-frame physical cube.
On one scene event every actual local stage with a positive scalar floor admits a genuine
finite Euclidean plan, with its exact density-law marginals and its own actual Neumann
budget divided by that floor. No common positive floor for the other classes is required. -/
theorem ae_all_originalOrientedStageDensities_exists_quadratic_coupling
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
      ∀ ρ : ℝ, 0 < ρ →
        ρ ≤ A.gamma s +
          (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ) / A.cubeVolume →
        ρ ≤ A.gamma t +
          (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ) / A.cubeVolume →
      ∀ ε : ℝ, 0 < ε →
      ∃ Γ : Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)) ×
          EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        Vlasov.IsCoupling Γ
          ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal (A.sourceDensity s t z))).map
            (EuclideanSpace.equiv _ ℝ).symm)
          ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal (A.targetDensity s t z))).map
            (EuclideanSpace.equiv _ ℝ).symm) ∧
        IsFiniteMeasure Γ ∧ Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
        (∫ z, dist z.1 z.2^2 ∂Γ) ≤
          ρ⁻¹ * originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene + ε := by
  let q := finrank ℝ S.covector.ker
  let cube := originalCenteredPhysicalCubeRegion b (2*R)
  let σ := volume.restrict cube
  have hc : IsCompact cube := isCompact_originalStagePhysicalCube b (2*R)
  obtain ⟨K, χ, hK, hχ⟩ := exists_originalNeumannTestCutoff cube hc
  refine ⟨K, hK, ?_⟩
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  have : IsFiniteMeasure σ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hc.measure_lt_top⟩
  have hσ : ∀ᵐ z ∂σ, z ∈ cube := ae_restrict_mem hc.measurableSet
  filter_upwards [D.ae_all_originalOrientedStageDensities_integrable_equal_mass
      hF hw Q b (by linarith : 0 ≤ ell) hR hRone hst,
    D.ae_all_originalOrientedStageResidualDensity_Neumann_bound
      hF hw hq hbounds Q b K hell hR hst hj] with scene hmass hbudget
  intro A hA ρ hρ hs ht ε hε
  have hAe : (⟨scene,A.sourceReserve,A.targetReserve,A.sourceKept,A.targetKept⟩ :
      OriginalOrientedStageResidualDensityData S w b R ell) = A := by
    cases A
    cases hA
    rfl
  have hm := hmass A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  dsimp only at hm
  rw [hAe] at hm
  have hσpos : 0 < σ.real univ := A.cubeVolume_pos hRpos
  have hl := A.densities_floor_of_local_scalar hs ht
  have hbound : ∀ ψ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z, ψ z ∂σ) = 0 →
      |∫ z, ψ z*(A.sourceDensity s t z-A.targetDensity s t z) ∂σ|^2 ≤
        originalOrientedStageCurrentInputNeumannBudget S w Q b K R ell s t hj scene *
          ‖smoothPhysicalGradientLtwo K σ ψ‖^2 := by
    intro ψ hψ
    rw [sq_abs]
    have hint : (∫ z, ψ z*(A.sourceDensity s t z-A.targetDensity s t z) ∂σ) =
        ∫ z, (A.sourceDensity s t z-A.targetDensity s t z)*ψ z ∂σ :=
      integral_congr_ae (Eventually.of_forall (fun z ↦ mul_comm (ψ z) _))
    rw [hint]
    exact hbudget A hA ψ hψ
  obtain ⟨π,hπ,hπfin,hπI,hπcost⟩ :=
    exists_originalDensity_quadratic_coupling_of_meanZero_squared_bound K σ hc hK χ hσ hχ hσpos
      (A.sourceDensity s t) (A.targetDensity s t) hm.1 hm.2.1 hρ
      (originalOrientedStageCurrentInputNeumannBudget_nonneg Q b K hRpos.le ell s t hj scene)
      (Eventually.of_forall (fun z ↦ (hl z).1))
      (Eventually.of_forall (fun z ↦ (hl z).2)) hm.2.2 hbound ε hε
  have : IsFiniteMeasure π := hπfin
  have hphys := originalRawQuadraticCoupling_toEuclidean _ _ π hπ hπI
  exact ⟨_,hphys.1,hphys.2.1,hphys.2.2.1,hphys.2.2.2.trans_le hπcost⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
