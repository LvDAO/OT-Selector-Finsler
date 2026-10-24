import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficCurrent
import OTSelector.Reconstruction.OriginalRetainedSlabResidualBoundaryCurrent
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalFaces
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedKernel

/-! The same actual oriented retained current vanishes on the true physical cube faces. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Actual zero vector values on the selected physical coordinate hyperplanes give zero
true-normal physical boundary pairing, including the original coordinate area measure. -/
theorem originalScreeningPhysicalCurrentBoundaryPairing_eq_zero {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (J : (Fin q → ℝ) → Fin q → ℝ) (R : ℝ)
    (hJ : ∀ z i, (orthonormalPhysicalCubeMap b).symm z i = R ∨
      (orthonormalPhysicalCubeMap b).symm z i = -R → J z = 0)
    (φ : (Fin q → ℝ) → ℝ) :
    originalScreeningPhysicalCurrentBoundaryPairing b J (2*R) φ = 0 := by
  cases q with
  | zero => rfl
  | succ r =>
    have hhalf : (2*R)/2 = R := by ring
    have hneg : -(2*R)/2 = -R := by ring
    have hz (a : Fin (r+1) × Fin 2) (y : Fin r → ℝ) :
        J (orthonormalPhysicalCubeMap b (a.1.insertNth (if a.2=0 then -R else R) y)) = 0 := by
      apply hJ _ a.1
      by_cases ha : a.2=0 <;> simp [ha]
    change originalPhysicalCubeVectorBoundaryPairing b J (2*R) φ = 0
    simp only [originalPhysicalCubeVectorBoundaryPairing, hhalf, hneg, hz, _root_.map_zero,
      zero_mul, integral_zero, mul_zero, Finset.sum_const_zero]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- On one original-scene event every actual oriented retained clock current vanishes on
all true physical cube faces, from the original path collar and the same canonical kernel. -/
theorem OriginalSeedConditionalMoments.ae_all_originalOrientedRetainedCurrent_eq_zero_on_physical_faces
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (z : Fin (finrank ℝ S.covector.ker) → ℝ) (i : Fin (finrank ℝ S.covector.ker)),
      (orthonormalPhysicalCubeMap b).symm z i = R ∨ (orthonormalPhysicalCubeMap b).symm z i = -R →
      originalPairRestrictedSeedPathClockSetCurrent S w (originalOrientedPathLengthRetained S w b R ell)
        (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene = 0 := by
  filter_upwards [D.ae_ae_original_pairKernel_interior_forward Q] with scene hlegal
  intro A z i hz
  unfold originalPairRestrictedSeedPathClockSetCurrent
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro c
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hlegal,
    ae_restrict_mem (measurableSet_originalOrientedPathLengthRetained S hF hw b R ell)] with a ha hret
  by_cases hc : c ∈ Ico a.2.1.1 a.2.1.2
  · have hpath := D.originalOrientedPathLengthRetained_path_mem_innerCube hF hw b
      (show 0 ≤ ell by linarith) hR hret ha.1 ha.2.1 (Ico_subset_Icc_self hc)
    have hh : 2*(R-originalStageFrameCollarFactor b*ell)/2 = R-originalStageFrameCollarFactor b*ell := by ring
    rw [mem_originalCenteredPhysicalCubeRegion_iff, hh] at hpath
    have hc1 : 1 ≤ originalStageFrameCollarFactor b*ell := by
      nlinarith [one_le_originalStageFrameCollarFactor b]
    have hn := hc1.trans (collar_le_norm_sub_of_inner_cube_face hpath i hz)
    have hηzero : originalEuclideanMollifier _ (originalSeedCompletePath S w a.1 a.2 c-z) = 0 := by
      rw [← originalEuclideanMollifier_inverse_frame b, map_sub]
      exact raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range _) _ hn
    rw [originalSeedCompletePath_eq_anchor_add_offset] at hηzero
    simp only [hηzero, zero_smul, Pi.zero_apply]
  · simp only [originalSeedClockOccupation_eq_indicator_velocity, indicator_of_notMem hc,
      smul_zero, Pi.zero_apply]

end OTSelector.Reconstruction
