import OTSelector.Reconstruction.OriginalBirthMaskedTraffic

/-! # Same-residue original birth traffic supplies the confined L2 coefficient -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual left pole internally supplies the short-window one-edge coefficient
C√s/t in the exact physical readout used by source-confined L2 recovery. -/
theorem exists_original_left_birth_maskedTraffic_canonicalMomentum_bound
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s A M₀ : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε → 0 ≤ A → 0 ≤ M₀ →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      ∀ J : Set ℝ, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, c - (S.level : ℝ) - D.lo ∈ Icc (t / 2) (4 * t)) →
      ∀ h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞,
      (∀ z, h z ≤ ENNReal.ofReal M₀) → ∀ mask : ℝ → ℝ≥0∞,
      (∀ c ∈ J, mask c ≤ 1) → mask.support ⊆ J →
      (∫⁻ c : ℝ, h (x + originalSeedPathOffset S w c m) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c)) ≤
        ENNReal.ofReal (M₀ * A * C * Real.sqrt s / t) *
          ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ := by
  obtain ⟨ε, C, hε, hεη, hC, hvel⟩ :=
    D.exists_original_left_birth_velocity_canonicalMomentum_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro t s A M₀ ht ht1 hs htε hA hM x m J hJ hvolume hclock h hh mask hmask hsupport
  apply original_maskedBirthTraffic_le_canonicalMomentum S w G ht hs hA hC.le hM
    x m hJ hvolume hh hmask hsupport
  intro c hc
  have hx := hvel ht ht1 hs htε (hclock c hc) (originalSeedPairMomentum S w m)
  have heq : D.lo + (c - (S.level : ℝ) - D.lo) = c - (S.level : ℝ) := by ring
  simpa only [heq] using hx

/-- Right-endpoint deaths have the same pointwise masked readout bound, with the
original clock, same residue, same birth frame, and arbitrary correlated mask. -/
theorem exists_original_right_birth_maskedTraffic_canonicalMomentum_bound
    {η : ℝ} (hη : 0 < η)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousAt Rem 0)
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ η ∧ 0 < C ∧
      ∀ {t s A M₀ : ℝ}, 0 < t → t ≤ 1 → 0 < s → 4 * t < ε → 0 ≤ A → 0 ≤ M₀ →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      ∀ J : Set ℝ, MeasurableSet J → volume J ≤ ENNReal.ofReal (A * s) →
      (∀ c ∈ J, D.hi - (c - (S.level : ℝ)) ∈ Icc (t / 2) (4 * t)) →
      ∀ h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞,
      (∀ z, h z ≤ ENNReal.ofReal M₀) → ∀ mask : ℝ → ℝ≥0∞,
      (∀ c ∈ J, mask c ≤ 1) → mask.support ⊆ J →
      (∫⁻ c : ℝ, h (x + originalSeedPathOffset S w c m) *
        (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c)) ≤
        ENNReal.ofReal (M₀ * A * C * Real.sqrt s / t) *
          ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖ := by
  obtain ⟨ε, C, hε, hεη, hC, hvel⟩ :=
    D.exists_original_right_birth_velocity_canonicalMomentum_bound hη hG hRem hpole
  refine ⟨ε, C, hε, hεη, hC, ?_⟩
  intro t s A M₀ ht ht1 hs htε hA hM x m J hJ hvolume hclock h hh mask hmask hsupport
  apply original_maskedBirthTraffic_le_canonicalMomentum S w G ht hs hA hC.le hM
    x m hJ hvolume hh hmask hsupport
  intro c hc
  simpa only [sub_sub_cancel] using
    hvel ht ht1 hs htε (hclock c hc) (originalSeedPairMomentum S w m)

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
