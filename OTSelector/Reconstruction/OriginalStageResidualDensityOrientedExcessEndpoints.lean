import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedGammaCancellation
import OTSelector.Reconstruction.OriginalStageReserveActualPhysicalMainCounts
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetWindowEndpoints

/-! Actual original excess removal gives both endpoint gamma equalities in the chosen frame. -/
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
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same actual physical-window main arrays and marks-only extreme-class deletion
produce both zero endpoint gammas internally. Original counts balance by deletion, true
clock support removes both full cuts, and retained cancellation is already proved. -/
theorem ae_all_originalOrientedStageExcessRemoval_endpoint_gamma_eq_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R)
    (hRone : 1 ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageExcessRemovalData (finrank ℝ S.covector.ker),
      IsOriginalStageMainPhysicalWindowArrays (originalCenteredPhysicalCubeRegion b (2 * R)) scene A.sourceMain A.targetMain →
      (∀ i : Fin A.sourceReserve.1, D.lo + (S.level : ℝ) < (A.sourceReserve.2 i).2 ∧
        (A.sourceReserve.2 i).2 < D.hi + (S.level : ℝ)) →
      (∀ i : Fin A.targetReserve.1, D.lo + (S.level : ℝ) < (A.targetReserve.2 i).2 ∧
        (A.targetReserve.2 i).2 < D.hi + (S.level : ℝ)) → A.hasCapacity →
      let B : OriginalOrientedStageResidualDensityData S w b R ell :=
        ⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩
      B.gamma (D.lo + (S.level : ℝ)) = 0 ∧ B.gamma (D.hi + (S.level : ℝ)) = 0 := by
  filter_upwards [D.ae_all_originalStageMainInputWindowPrefix_extremes Q,
    D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone (D.lo + (S.level : ℝ)),
    D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone (D.hi + (S.level : ℝ))]
    with scene hread hlo hhi
  intro A harray hs ht hcap
  dsimp only
  let B : OriginalOrientedStageResidualDensityData S w b R ell :=
    ⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩
  have hreserve := originalStageRemainingReservePrefix_extremes A.sourceReserve A.targetReserve A.sourceKept A.targetKept hs ht
  have hdelta0 : originalOrientedStageFullCutError S w b R (D.lo + (S.level : ℝ)) scene = 0 := by
    rw [originalOrientedStageFullCutError, (hread.2.2 _).1, hread.1]
    simp only [integral_zero_measure, integral_zero, sub_self]
  have hdeltam : originalOrientedStageFullCutError S w b R (D.hi + (S.level : ℝ)) scene =
      (A.sourceMain.1 : ℝ) - A.targetMain.1 := by
    rw [originalOrientedStageFullCutError, (hread.2.2 _).2, hread.2.1,
      harray.actual_counts.1, harray.actual_counts.2]
    simp only [integral_zero_measure, integral_zero, sub_zero]
  have hbalance : (A.sourceMain.1 : ℝ) + A.sourceKept.card = (A.targetMain.1 : ℝ) + A.targetKept.card := by
    exact_mod_cast (A.removal_counts_and_balance hcap).2.2
  constructor
  · rw [hlo A.sourceReserve A.targetReserve A.sourceKept A.targetKept, hdelta0]
    change (originalStageRemainingReservePrefix _ _ _ _ _ + 0) / B.cubeVolume = 0
    rw [hreserve.1]
    simp
  · rw [hhi A.sourceReserve A.targetReserve A.sourceKept A.targetKept, hdeltam]
    change (originalStageRemainingReservePrefix _ _ _ _ _ + ((A.sourceMain.1 : ℝ) - A.targetMain.1)) / B.cubeVolume = 0
    rw [hreserve.2, show (A.sourceKept.card : ℝ) - A.targetKept.card + ((A.sourceMain.1 : ℝ) - A.targetMain.1) = 0 by linarith]
    exact zero_div _

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
