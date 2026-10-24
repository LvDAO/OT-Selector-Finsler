import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalKinetic

/-! The actual original focal kinetic and bounded marked reward satisfy the
physical Euclidean cost bound used by the original-index screening comparator. -/
open Set MeasureTheory Module Manifold
open scoped BigOperators ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The true original focal matrix bound supplies one nonnegative physical
quadratic constant for all original marks and positions. The same signed marked
cost pays exactly the bounded reward term |t|G on each repaired original edge. -/
theorem exists_originalFocalMarkedCost_physical_quadratic_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (g : ℝ → ℝ → ℝ) {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ C ≥ 0, ∀ (a b : ℝ) (x y : Fin (finrank ℝ S.covector.ker) → ℝ) (t : ℝ),
      D.originalFocalKinetic gap a b (y-x)-t*g a b ≤
        C*dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2+|t| * G := by
  obtain ⟨C, hC, hk⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  refine ⟨C, hC, ?_⟩
  intro a b x y t
  have hread : (∑ i, (y-x) i^2) =
      dist ((EuclideanSpace.equiv _ ℝ).symm x) ((EuclideanSpace.equiv _ ℝ).symm y)^2 := by
    rw [dist_comm, dist_eq_norm, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    rfl
  have hreward : -(t*g a b) ≤ |t| * G := by
    calc
      _ ≤ |t*g a b| := neg_le_abs _
      _ = |t| * |g a b| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgb a b) (abs_nonneg t)
  have hkin := (le_abs_self (D.originalFocalKinetic gap a b (y-x))).trans (hk a b (y-x))
  rw [hread] at hkin
  linarith
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
