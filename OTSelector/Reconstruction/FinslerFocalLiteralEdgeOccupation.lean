import OTSelector.Reconstruction.LiteralCompletePathMaskedOccupation

/-! Original focal geometry supplies literal full-clock masked edge occupation bounds. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original left endpoint produces literal full-clock edge bounds.
The physical constant retains the original kernel and has no normalizing-matrix factor. -/
theorem exists_original_left_focal_maskedCompletePathEdgeTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, δ > 0 ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |c - S.level - D.lo - a| ≤ σ * a) →
      ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker),
      e.1.2 - S.level ∈ Ioo D.lo D.hi →
      ∀ R M : ℝ, 0 ≤ R → 0 ≤ M →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M) → (∀ x, R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞,
      (∀ c ∈ Icc l r, mask ((physicalPairAnchor e).2, c) ≤ 1) →
      (∀ c ∉ Icc l r, mask ((physicalPairAnchor e).2, c) = 0) →
      originalMaskedCompletePathEdgeTraffic S w η mask e ≤ ENNReal.ofReal
        ((4 * M * (R + 1)) * min 1 ((r - l) *
          ‖originalSeedKernel S w (D.lo + a) *ᵥ
            originalSeedPairMomentum S w (physicalPairAnchor e).2‖)) ∧
      (originalMaskedCompletePathEdgeTraffic S w η mask e).toReal ≤ 4 * M * (R + 1) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hterminal⟩ :=
    D.exists_original_left_focal_oneEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro a ha l r hlr hband e he R M hR hM η hη0 hηM hηR mask hmask hmaskZero
  have hb : originalMaskedCompletePathEdgeTraffic S w η mask e ≤ ENNReal.ofReal
      ((4 * M * (R + 1)) * min 1 ((r - l) *
        ‖originalSeedKernel S w (D.lo + a) *ᵥ
          originalSeedPairMomentum S w (physicalPairAnchor e).2‖)) := by
    rw [originalMaskedCompletePathEdgeTraffic_eq_setLIntegral S w η mask e l r hmaskZero]
    apply hterminal a ha l r hlr hband e.1.1 (physicalPairAnchor e).2 he R M hR hM
    · intro c hc
      exact original_maskedOccupation_speed_bound S w e.1.1 (physicalPairAnchor e).2
        (mask := fun c ↦ mask ((physicalPairAnchor e).2, c)) (c := c) hη0 hηM (hmask c hc)
    · intro c hc hRout
      rw [hηR _ hRout, ENNReal.ofReal_zero, zero_mul, zero_mul]
  refine ⟨hb, ?_⟩
  have hC : 0 ≤ 4 * M * (R + 1) := by positivity
  apply ENNReal.toReal_le_of_le_ofReal hC
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right hC (min_le_left _ _)))

/-- The actual original right endpoint produces literal full-clock edge bounds.
The physical constant retains the original kernel and has no normalizing-matrix factor. -/
theorem exists_original_right_focal_maskedCompletePathEdgeTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, δ > 0 ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |D.hi - (c - S.level) - a| ≤ σ * a) →
      ∀ e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker),
      e.1.2 - S.level ∈ Ioo D.lo D.hi →
      ∀ R M : ℝ, 0 ≤ R → 0 ≤ M →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M) → (∀ x, R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞,
      (∀ c ∈ Icc l r, mask ((physicalPairAnchor e).2, c) ≤ 1) →
      (∀ c ∉ Icc l r, mask ((physicalPairAnchor e).2, c) = 0) →
      originalMaskedCompletePathEdgeTraffic S w η mask e ≤ ENNReal.ofReal
        ((4 * M * (R + 1)) * min 1 ((r - l) *
          ‖originalSeedKernel S w (D.hi - a) *ᵥ
            originalSeedPairMomentum S w (physicalPairAnchor e).2‖)) ∧
      (originalMaskedCompletePathEdgeTraffic S w η mask e).toReal ≤ 4 * M * (R + 1) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hterminal⟩ :=
    D.exists_original_right_focal_oneEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro a ha l r hlr hband e he R M hR hM η hη0 hηM hηR mask hmask hmaskZero
  have hb : originalMaskedCompletePathEdgeTraffic S w η mask e ≤ ENNReal.ofReal
      ((4 * M * (R + 1)) * min 1 ((r - l) *
        ‖originalSeedKernel S w (D.hi - a) *ᵥ
          originalSeedPairMomentum S w (physicalPairAnchor e).2‖)) := by
    rw [originalMaskedCompletePathEdgeTraffic_eq_setLIntegral S w η mask e l r hmaskZero]
    apply hterminal a ha l r hlr hband e.1.1 (physicalPairAnchor e).2 he R M hR hM
    · intro c hc
      exact original_maskedOccupation_speed_bound S w e.1.1 (physicalPairAnchor e).2
        (mask := fun c ↦ mask ((physicalPairAnchor e).2, c)) (c := c) hη0 hηM (hmask c hc)
    · intro c hc hRout
      rw [hηR _ hRout, ENNReal.ofReal_zero, zero_mul, zero_mul]
  refine ⟨hb, ?_⟩
  have hC : 0 ≤ 4 * M * (R + 1) := by positivity
  apply ENNReal.toReal_le_of_le_ofReal hC
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right hC (min_le_left _ _)))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
