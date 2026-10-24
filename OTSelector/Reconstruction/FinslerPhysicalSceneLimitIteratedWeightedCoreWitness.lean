import OTSelector.Reconstruction.FinslerPhysicalSceneLimitIteratedCoreWitness

/-!
# Core-dependent positive physical cycle margins in the same iterated scene

Each auxiliary endpoint core may have its own positive physical four-edge margin.
It is fixed before either weak limit. Dividing its estimate removes the margin
without requiring a uniform positive bound across core accuracy.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- Positive margins can depend on auxiliary core accuracy; the same scene is
first limited in sample size, then in tilt, and finally in discarded mass. -/
theorem ae_eq_zero_of_iterated_weak_lsc_weighted_core_accuracy_bounds
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ k, Tendsto (φ k) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ k, Tendsto (fun N ↦ Pn k (φ k N)) atTop (𝓝 (Q k)))
    (houter : Tendsto (fun k ↦ Q (ψ k)) atTop (𝓝 R))
    (W : S → ℝ≥0∞) (hW : LowerSemicontinuous W)
    (accuracy : ℕ → ℝ≥0∞) (haccuracy : Tendsto accuracy atTop (𝓝 0))
    (weight : ℕ → ℝ≥0∞) (hw0 : ∀ m, weight m ≠ 0) (hwt : ∀ m, weight m ≠ ⊤)
    (hbound : ∀ m, ∃ B : ℕ → ℝ≥0∞, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ᶠ N in atTop,
        weight m * (∫⁻ s, W s ∂(Pn k N : Measure S)) ≤ B k + weight m * accuracy m) :
    ∀ᵐ s ∂(R : Measure S), W s = 0 := by
  apply ae_eq_zero_of_iterated_weak_lsc_tilt_and_core_accuracy_bounds
    Pn Q R φ hφ ψ hψ hinner houter W hW accuracy haccuracy
  intro m
  obtain ⟨B, hB, hb⟩ := hbound m
  refine ⟨fun k ↦ B k / weight m, ?_, ?_⟩
  · simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hB (Or.inr (hw0 m))
  · filter_upwards [hb] with k hk
    filter_upwards [hk] with N hN
    apply (ENNReal.mul_le_mul_iff_right (hw0 m) (hwt m)).mp
    simpa only [mul_add, ENNReal.mul_div_cancel (hw0 m) (hwt m)] using hN

end OTSelector.Reconstruction
