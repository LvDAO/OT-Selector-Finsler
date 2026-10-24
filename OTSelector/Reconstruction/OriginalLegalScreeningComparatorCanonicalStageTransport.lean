import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannCutoff
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannTransport
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetCanonical
import OTSelector.Reconstruction.OriginalStageResidualDensityUniformReserves

/-! Actual same-scene canonical stage densities produce genuine finite transport
on the actual good-cut event, using their original Neumann energy budget. -/
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

/-- A true test carrier is chosen before the scene event. On that single event every
actual reserve choice on two good proper cuts has a genuine finite transport plan
between its actual density laws. Its literal Euclidean cost pays only its own same-scene
Neumann budget divided by the actual 3r floor, plus arbitrary epsilon. -/
theorem ae_all_originalCanonicalStageDensities_exists_quadratic_coupling
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
        A.scene = scene → ∀ r : ℝ, 0 < r → A.goodCut r s → A.goodCut r t →
      ∀ ε : ℝ, 0 < ε → ∃ π : Measure ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
          (Fin (finrank ℝ S.covector.ker) → ℝ)),
        Vlasov.IsCoupling π
          ((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (A.sourceDensity s t z)))
          ((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (A.targetDensity s t z))) ∧
        IsFiniteMeasure π ∧
        Integrable (fun z ↦ ‖(EuclideanSpace.equiv _ ℝ).symm z.2-
          (EuclideanSpace.equiv _ ℝ).symm z.1‖^2) π ∧
        (∫ z, ‖(EuclideanSpace.equiv _ ℝ).symm z.2-
          (EuclideanSpace.equiv _ ℝ).symm z.1‖^2 ∂π) ≤
          (3*r)⁻¹ * originalCanonicalStageNeumannBudget S w K R ell s t scene + ε := by
  obtain ⟨K, χ, hK, hχ⟩ := exists_originalNeumannTestCutoff
    (haarRootCube (Fin (finrank ℝ S.covector.ker)) R) isCompact_Icc
  refine ⟨K, hK, ?_⟩
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
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
  have hη := (contDiff_originalEuclideanMollifier q).continuous
  have hfloor := D.ae_all_originalStageDensities_floor_on_goodCuts hF hw Q hell hR s t
    hη (hasCompactSupport_originalEuclideanMollifier q) (integrable_originalEuclideanMollifier q)
    (originalEuclideanMollifier_nonneg q) (integral_originalEuclideanMollifier_eq_one q)
    (raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q))
    (coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q))
    (abs_originalEuclideanMollifier_le q)
  filter_upwards [D.ae_all_originalCanonicalStageDensities_integrable_equal_mass_uniform_reserves
      hF hw Q hell hR hst,
    D.ae_all_originalCanonicalStageResidualDensity_Neumann_bound hF hw hq hbounds Q hell hR hst K,
    hfloor] with scene hmass hbudget hfloor
  intro A hA r hr hgs hgt ε hε
  have hAe : (⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩ :
      OriginalStageResidualDensityData S w R ell η) = A := by
    cases A
    cases hA
    rfl
  have hm := hmass A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  have hl := hfloor A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  dsimp only at hm hl
  rw [hAe] at hm hl
  have hbound : ∀ ψ : 𝓓_{K}(Fin q → ℝ, ℝ), (∫ z, ψ z ∂σ) = 0 →
      |∫ z, ψ z * (A.sourceDensity s t z-A.targetDensity s t z) ∂σ|^2 ≤
        originalCanonicalStageNeumannBudget S w K R ell s t scene *
          ‖smoothPhysicalGradientLtwo K σ ψ‖^2 := by
    intro ψ hψ
    simpa only [mul_comm, sq_abs] using hbudget A hA ψ hψ
  exact exists_originalDensity_quadratic_coupling_of_meanZero_squared_bound K σ
    isCompact_Icc hK χ hσ hχ hσpos (A.sourceDensity s t) (A.targetDensity s t)
    hm.1 hm.2.1 (by positivity : 0 < 3*r)
    (originalCanonicalStageNeumannBudget_nonneg S w K hRpos.le ell s t scene)
    (Filter.Eventually.of_forall (fun z ↦ (hl r hgs hgt z).1))
    (Filter.Eventually.of_forall (fun z ↦ (hl r hgs hgt z).2)) hm.2.2 hbound ε hε
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
