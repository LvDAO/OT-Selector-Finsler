import OTSelector.Reconstruction.FinslerFocalLiteralEdgeOccupation

/-! The already proved actual physical min-one estimate gives a uniform literal
pair-kernel edge bound. Ineligible unoccupied pairs vanish through their own mask. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The original left geometry supplies the physical constant `4 M (R+1)`
for the literal full-clock pair readout, including all mask-zero edge cases. -/
theorem OriginalSeedConditionalMoments.exists_original_left_focal_maskedPairTraffic_uniform_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |c - S.level - D.lo - a| ≤ σ * a) →
      ∀ R M₀ : ℝ, 0 ≤ R → 0 ≤ M₀ →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) → (∀ x, R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞,
      (∀ z, mask z ≤ 1) → (∀ m c, c ∉ Icc l r → mask (m, c) = 0) →
      (∀ m c, mask (m, c) ≠ 0 → m.1.1 - S.level ∈ Ioo D.lo D.hi) →
      ∀ (x : Fin (finrank ℝ S.covector.ker) → ℝ)
        (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))) ≤
          ENNReal.ofReal (4 * M₀ * (R + 1)) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hbound⟩ :=
    D.exists_original_left_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro a ha l r hlr hband R M₀ hR hM η hη0 hηM hηR mask hm hz hi x m
  by_cases hs : m.1.1 - S.level ∈ Ioo D.lo D.hi
  · let e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) :=
      ((x, m.1.1), (x + m.2, m.1.2))
    have he : physicalPairAnchor e = (x, m) := by
      simp only [physicalPairAnchor, e, add_sub_cancel_left]
    have hb := (hbound a ha l r hlr hband e hs R M₀ hR hM η hη0 hηM hηR
      mask (by intro c _; simpa only [he] using hm (m, c))
      (by intro c hc; simpa only [he] using hz m c hc)).1
    have hb' := hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (show 0 ≤ 4 * M₀ * (R + 1) by positivity) (min_le_left _ _)))
    simpa only [originalMaskedCompletePathEdgeTraffic, legalMarkedCompletePathEdgeTraffic, he,
      e] using hb'
  · have hmzero : ∀ c : ℝ, mask (m, c) = 0 := fun c ↦
      not_ne_iff.mp (fun hn ↦ hs (hi m c hn))
    simp only [hmzero, mul_zero, lintegral_zero, zero_le]

/-- The original right geometry supplies the physical constant `4 M (R+1)`
for the literal full-clock pair readout, including all mask-zero edge cases. -/
theorem OriginalSeedConditionalMoments.exists_original_right_focal_maskedPairTraffic_uniform_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) δ, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |D.hi - (c - S.level) - a| ≤ σ * a) →
      ∀ R M₀ : ℝ, 0 ≤ R → 0 ≤ M₀ →
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
      (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) → (∀ x, R < ‖x‖ → η x = 0) →
      ∀ mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞,
      (∀ z, mask z ≤ 1) → (∀ m c, c ∉ Icc l r → mask (m, c) = 0) →
      (∀ m c, mask (m, c) ≠ 0 → m.1.1 - S.level ∈ Ioo D.lo D.hi) →
      ∀ (x : Fin (finrank ℝ S.covector.ker) → ℝ)
        (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask (m, c))) ≤
          ENNReal.ofReal (4 * M₀ * (R + 1)) := by
  obtain ⟨δ, hδ, hδspan, σ, hσ, hσhalf, hbound⟩ :=
    D.exists_original_right_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ, hδ, hδspan, σ, hσ, hσhalf, ?_⟩
  intro a ha l r hlr hband R M₀ hR hM η hη0 hηM hηR mask hm hz hi x m
  by_cases hs : m.1.1 - S.level ∈ Ioo D.lo D.hi
  · let e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) :=
      ((x, m.1.1), (x + m.2, m.1.2))
    have he : physicalPairAnchor e = (x, m) := by
      simp only [physicalPairAnchor, e, add_sub_cancel_left]
    have hb := (hbound a ha l r hlr hband e hs R M₀ hR hM η hη0 hηM hηR
      mask (by intro c _; simpa only [he] using hm (m, c))
      (by intro c hc; simpa only [he] using hz m c hc)).1
    have hb' := hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right (show 0 ≤ 4 * M₀ * (R + 1) by positivity) (min_le_left _ _)))
    simpa only [originalMaskedCompletePathEdgeTraffic, legalMarkedCompletePathEdgeTraffic, he,
      e] using hb'
  · have hmzero : ∀ c : ℝ, mask (m, c) = 0 := fun c ↦
      not_ne_iff.mp (fun hn ↦ hs (hi m c hn))
    simp only [hmzero, mul_zero, lintegral_zero, zero_le]

end OTSelector.Reconstruction
