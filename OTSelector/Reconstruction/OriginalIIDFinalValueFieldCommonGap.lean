import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation
import OTSelector.Transport.Calibration.CompactClockGap

/-! One genuine positive gap for the same physical carriers and original conditional laws. -/
open Set MeasureTheory ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction

/-- Decreasing the original conditional support gap keeps both compact supports
and their original diameter bound. -/
theorem ConditionalClockSupportBounds.mono_gap
    {μ ν : Measure ℝ} {gap small diameter : ℝ}
    (h : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : small ≤ gap) :
    ConditionalClockSupportBounds μ ν small diameter where
  source_compact := h.source_compact
  target_compact := h.target_compact
  separated := fun s hs t ht ↦ hsmall.trans (h.separated s hs t ht)
  diameter := h.diameter

/-- The unchanged chosen atlas's conditional gap and the actual compact physical
carrier gap give one common positive gap, with no new separation assumption. -/
theorem exists_original_common_physical_conditional_gap
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Z]
    (u : M → ℝ) (a : M → Z) (lambda : Measure Z)
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda μ ν gap diameter) :
    ∃ common : ℝ, 0 < common ∧
      (∀ x ∈ A, ∀ y ∈ B, common ≤ dist x y) ∧
      PopulationConditionalSeparationLaw u a lambda μ ν common diameter := by
  obtain ⟨physical,hphysical,hdist⟩ := exists_original_support_gap hA hB hAB
  refine ⟨min gap physical,lt_min hgap hphysical,?_,?_⟩
  · intro x hx y hy
    exact (min_le_right _ _).trans (hdist x hx y hy)
  · exact hsep.mono (fun _ hz ↦ hz.mono_gap (min_le_left _ _))

end OTSelector.Reconstruction
