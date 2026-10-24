import OTSelector.Reconstruction.OriginalRegularBirthGeometry
import OTSelector.Reconstruction.OriginalMaskedOneEdgeTraffic

/-! Literal original regular-birth traffic in its actual scalar frame. A uniform
physical velocity cone gives the min-one estimate, retaining the sqrt(s) gain
for short physical windows and arbitrary masks of the same occupied edges. -/
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

/-- The original compact regular strip supplies its own uniform physical
min-one traffic estimate in every scalar birth frame s I. -/
theorem exists_original_regular_birth_maskedTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b A : ℝ} (hA : 0 ≤ A)
    (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ c ∈ Icc a b,
      ∀ {l r s R M₀ : ℝ}, l ≤ r → 0 < s → r - l ≤ A * s →
      (∀ v ∈ Icc l r, |v - c| ≤ δ) → 0 ≤ R → 0 ≤ M₀ →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      m.1.1 - S.level ∈ Ioo D.lo D.hi →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ z, 0 ≤ η z) → (∀ z, η z ≤ M₀) → (∀ z, R < ‖z‖ → η z = 0) →
      ∀ mask : ℝ → ℝ≥0∞, (∀ v ∈ Icc l r, mask v ≤ 1) →
      (∫⁻ v in Icc l r, ENNReal.ofReal (η (originalSeedCompletePath S w x m v)) *
        ENNReal.ofReal ‖originalSeedClockOccupation S w v m‖ * mask v) ≤
      ENNReal.ofReal ((4 * M₀ * (R + 1)) * min 1
        ((C * Real.sqrt s) *
          ‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
            (Fin (finrank ℝ S.covector.ker)) ℝ)))ᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖)) := by
  obtain ⟨B, δ, hB, hδ, hnorm, hcone⟩ := D.exists_original_regular_strip_uniformCone hF hw ha hb
  refine ⟨A * B * Real.sqrt (finrank ℝ S.covector.ker : ℝ), δ, by positivity, hδ, ?_⟩
  intro c hc l r s R M₀ hlr hs hlen hwin hR hM x m hm η hη hηM hηR mask hmask
  have ht := D.original_maskedOneEdgeTraffic_le_min_one_of_physicalCone hF hw x m hm hlr hR hM
    (fun v hv ↦ (hcone c hc v (hwin v hv)).1)
    (fun v hv ↦ (hcone c hc v (hwin v hv)).2 _) hη hηM hηR hmask
  have hv := regular_birth_window_velocity_le_canonicalMomentum hs hB.le hA hlen
    (hnorm c hc) (originalSeedPairMomentum S w m)
  simp only [Fintype.card_fin] at hv
  exact ht.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_min_left 1 hv) (by positivity)))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
