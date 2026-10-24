import OTSelector.Reconstruction.OriginalRegularOneEdgeTraffic
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability
import OTSelector.MeasureTheory.Integral.AERestriction

/-! Regular actual geometry supplies a full-clock one-edge traffic bound for
every original anchor and paired mark, including pairs excluded by the actual
clock mask. The physical bound has no normalization-matrix factor. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- A genuine regular reference clock produces the same physical one-edge
bound on the literal full-clock integral, including zeroed-out original pairs. -/
theorem exists_original_regular_fullClock_edge_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {cut : ℝ}
    (hcut : cut - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {l r R M₀ : ℝ}, l ≤ r →
      (∀ c ∈ Icc l r, |c - cut| ≤ δ) → 0 ≤ R → 0 ≤ M₀ →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ z, 0 ≤ η z) → (∀ z, η z ≤ M₀) → (∀ z, R < ‖z‖ → η z = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞,
      (∀ z, mask z ≤ 1) → (∀ m c, c ∉ Icc l r → mask (m, c) = 0) →
      (∀ m c, mask (m, c) ≠ 0 → m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi) →
      ∀ (x : Fin (finrank ℝ S.covector.ker) → ℝ)
        (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)) ∂volume) ≤
        ENNReal.ofReal (4 * M₀ * (R + 1)) := by
  obtain ⟨δ, hδ, hcone⟩ := D.exists_original_regular_physicalVelocityCone hF hw hcut
  refine ⟨δ, hδ, ?_⟩
  intro l r R M₀ hlr hwin hR hM η hη hηM hηR mask hm hmzero hsource x m
  by_cases ha : m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi
  · have hloc := D.original_maskedOneEdgeTraffic_le_min_one_of_physicalCone hF hw x m ha hlr hR hM
      (fun c hc ↦ (hcone c (hwin c hc)).1)
      (fun c hc ↦ (hcone c (hwin c hc)).2 _) hη hηM hηR
      (fun c _ ↦ hm (m, c))
    have heq := OTSelector.Probability.setLIntegral_eq_of_ae_zero_outside
      (μ := (volume : Measure ℝ)) measurableSet_Icc
      (u := fun c : ℝ ↦ ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c)))
      (ae_of_all _ (fun c hc ↦ by rw [hmzero m c hc, mul_zero, mul_zero]))
    rw [← heq]
    have hloc' : (∫⁻ c in Icc l r, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))) ≤
        ENNReal.ofReal ((4 * M₀ * (R + 1)) * min 1
          ((r - l) * ‖originalSeedKernel S w (cut - S.level) *ᵥ originalSeedPairMomentum S w m‖)) := by
      simpa only [originalSeedCompletePath_eq_anchor_add_offset, mul_assoc] using hloc
    exact hloc'.trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (by positivity) (min_le_left _ _)))
  · have hz : ∀ c : ℝ, mask (m, c) = 0 := by
      intro c
      by_contra hn
      exact ha (hsource m c hn)
    simp only [hz, mul_zero, lintegral_zero]
    exact zero_le

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
