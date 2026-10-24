import OTSelector.Reconstruction.OriginalLegalScreeningComparatorFocalCost
import OTSelector.Reconstruction.OriginalStagePhysicalPortKernelSupport
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoCycleDefect

/-! Actual same-frame cube geometry pays for extra forward block repairs. -/
open Set Function MeasureTheory Module Manifold
open scoped BigOperators ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm

/-- Genuine Euclidean square diameter of the actual chosen physical cube.
The factor q comes from the finite coordinate sum, rather than identifying
the raw coordinate norm with the Euclidean norm. -/
theorem originalOrientedPhysicalCube_square_distance_le {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (_hR : 0 ≤ R)
    {x y : Fin q → ℝ} (hx : x ∈ originalCenteredPhysicalCubeRegion b (2*R))
    (hy : y ∈ originalCenteredPhysicalCubeRegion b (2*R)) :
    dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2 ≤
      4 * (q : ℝ) * R^2 := by
  have hx' := (mem_originalCenteredPhysicalCubeRegion_iff b (2*R) x).mp hx
  have hy' := (mem_originalCenteredPhysicalCubeRegion_iff b (2*R) y).mp hy
  rw [show 2*R/2 = R by ring] at hx' hy'
  rw [dist_eq_norm, ← map_sub, ← norm_euclidean_inverse_originalStageFrame b (x-y),
    map_sub, EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin q, (2*R)^2 := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(orthonormalPhysicalCubeMap b).symm x i -
        (orthonormalPhysicalCubeMap b).symm y i‖^2 ≤ (2*R)^2
      have hab : |(orthonormalPhysicalCubeMap b).symm x i -
          (orthonormalPhysicalCubeMap b).symm y i| ≤ 2*R := by
        apply abs_le.mpr
        constructor
        · linarith [hx'.1 i,hy'.2 i]
        · linarith [hx'.2 i,hy'.1 i]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hab) _
    _ = _ := by simp; ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual focal coefficient gives a uniform cost for every new original
pair inside the same cube. This supplies the block completion's coarse
quadratic cost without a repaired-cost oracle. -/
theorem exists_originalFocalMarkedCost_orientedCube_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (g : ℝ → ℝ → ℝ) {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ C ≥ 0, ∀ (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R : ℝ), 0 ≤ R →
      ∀ x y : LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        x.1 ∈ originalCenteredPhysicalCubeRegion b (2*R) →
        y.1 ∈ originalCenteredPhysicalCubeRegion b (2*R) → ∀ t : ℝ,
          originalWeightedEdgeCost (D.originalFocalKinetic gap) g t (x,y) ≤
            4*C*(finrank ℝ S.covector.ker : ℝ)*R^2 + |t| * G := by
  obtain ⟨C,hC,hcost⟩ := D.exists_originalFocalMarkedCost_physical_quadratic_bound hF hw hgap hbounds g hgb
  refine ⟨C,hC,?_⟩
  intro b R hR x y hx hy t
  have hc := hcost x.2 y.2 x.1 y.1 (-t)
  have hd := originalOrientedPhysicalCube_square_distance_le b hR hx hy
  have hcd := mul_le_mul_of_nonneg_left hd hC
  dsimp only [originalWeightedEdgeCost]
  simp only [abs_neg, neg_mul, sub_neg_eq_add] at hc
  nlinarith only [hc,hcd]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
