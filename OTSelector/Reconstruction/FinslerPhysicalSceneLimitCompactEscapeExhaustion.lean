import OTSelector.Reconstruction.FinslerPhysicalSceneLimitCompactExhaustionDomination

/-!
# Vanishing compact escape bounds for one fixed scene
-/

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- Uniform eventual compact escape control supplies one genuine compact
exhaustion with a quantitative null tolerance sequence. The compact sets may be
chosen after their auxiliary estimates; the underlying readouts remain fixed. -/
theorem exists_physicalScene_compact_exhaustion_escape_bounds
    {I Y : Type*} [TopologicalSpace Y] (K : CompactExhaustion Y)
    (tail : I → ℕ → Set Y → ℝ≥0∞)
    (hmono : ∀ i N, Antitone (tail i N))
    (hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ∃ L : Set Y, IsCompact L ∧
      ∀ᶠ N in atTop, ∀ i, tail i N L ≤ ε) :
    ∃ K' : CompactExhaustion Y, ∀ R : ℕ,
      ∀ᶠ N in atTop, ∀ i, tail i N (K' R) ≤ (((R + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
  have hpos (R : ℕ) : (0 : ℝ≥0∞) < (((R + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    simp
  choose L hL hb using fun R ↦ hsmall _ (hpos R)
  obtain ⟨K', hK'⟩ := exists_physicalScene_compact_exhaustion_domination K L hL
  refine ⟨K', ?_⟩
  intro R
  filter_upwards [hb R] with N hN i
  exact (hmono i N (hK' R)).trans (hN i)

/-- The tolerances used in the actual compact escape construction tend to
zero independently of the sample and tilt indices. -/
theorem tendsto_physicalScene_compact_escape_tolerance_zero :
    Tendsto (fun R : ℕ ↦ (((R + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
  ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

end OTSelector.Reconstruction
