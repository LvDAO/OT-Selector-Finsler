import OTSelector.Reconstruction.OriginalFocalOneEdgeTraffic

/-!
# Literal original occupation and restricted one-edge traffic

The half-open original clock occupation is dominated by its own actual velocity.
Every pointwise edge mask between zero and one therefore satisfies the physical
one-edge bound on the same original path. This includes adaptive restrictions.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual half-open clock occupation never exceeds its own unchanged physical velocity. -/
theorem norm_originalSeedClockOccupation_le_velocity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (c : ℝ) : ‖originalSeedClockOccupation S w c m‖ ≤
      ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖ := by
  rw [originalSeedClockOccupation_eq_indicator_velocity]
  by_cases hc : c ∈ Ico m.1.1 m.1.2
  · simp only [indicator_of_mem hc, le_refl]
  · simp only [indicator_of_notMem hc, norm_zero]
    exact norm_nonneg _

/-- A literal original masked occupation is bounded by the actual physical speed. -/
theorem original_maskedOccupation_speed_bound (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {M : ℝ}
    (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    {mask : ℝ → ℝ≥0∞} {c : ℝ} (hmask : mask c ≤ 1) :
    ENNReal.ofReal (η (originalSeedCompletePath S w x m c)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c ≤
        ENNReal.ofReal (M *
          ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖) := by
  calc
    _ ≤ ENNReal.ofReal (η (originalSeedCompletePath S w x m c)) *
        ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * 1 :=
      mul_le_mul_right hmask _
    _ = ENNReal.ofReal (η (originalSeedCompletePath S w x m c) *
        ‖originalSeedClockOccupation S w c m‖) := by
      rw [mul_one, ENNReal.ofReal_mul (hη0 _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul (hηM _) (norm_originalSeedClockOccupation_le_velocity S w m c)
        (norm_nonneg _) (le_trans (hη0 0) (hηM 0)))

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original occupation, with any mask bounded by one, has the physical min-one bound. -/
theorem original_maskedOneEdgeTraffic_le_min_one_of_physicalCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - S.level ∈ Ioo D.lo D.hi)
    {l r R M : ℝ} (hlr : l ≤ r) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hclock : ∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi)
    {v : Fin (finrank ℝ S.covector.ker) → ℝ}
    (hcone : ∀ c ∈ Icc l r,
      ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m - v‖ ≤ ‖v‖ / 4)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη0 : ∀ z, 0 ≤ η z) (hηM : ∀ z, η z ≤ M)
    (hηR : ∀ z, R < ‖z‖ → η z = 0)
    {mask : ℝ → ℝ≥0∞} (hmask : ∀ c ∈ Icc l r, mask c ≤ 1) :
    (∫⁻ c in Icc l r, ENNReal.ofReal (η (originalSeedCompletePath S w x m c)) *
      ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c) ≤
        ENNReal.ofReal ((4 * M * (R + 1)) * min 1 ((r - l) * ‖v‖)) := by
  apply D.original_oneEdgeTraffic_le_min_one_of_physicalCone hF hw x m ha hlr hR hM hclock
    hcone (fun c hc ↦ original_maskedOccupation_speed_bound S w x m hη0 hηM (hmask c hc))
  intro c hc hRout
  rw [hηR _ hRout, ENNReal.ofReal_zero, zero_mul, zero_mul]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
