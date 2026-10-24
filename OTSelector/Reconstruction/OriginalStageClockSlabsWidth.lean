import OTSelector.Reconstruction.OriginalStageClockSlabsSupport

/-! Expose the actual short grid for samplewise original-atom class legality. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
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

omit [BorelSpace E] in
/-- The real conditional support span itself supplies the short-width grid used to assign
all original atom labels, alongside the exact two analytic slab measure decompositions. -/
theorem exists_originalShortClockSlabGrid {δ diameter : ℝ}
    (hδ : 0 < δ) (_hsep : ConditionalClockSupportBounds μ ν δ diameter) :
    ∃ G : OriginalStageClockGrid, 0 < G.count ∧
      G.cut 0 = D.lo + (S.level : ℝ) ∧ G.cut G.count = D.hi + (S.level : ℝ) ∧
      (∀ i : Fin G.count, G.cut (i + 1) - G.cut i < δ) ∧
      (∑ i, μ.restrict (G.sourceCell i)) = μ ∧
      (∑ i, ν.restrict (G.targetCell i)) = ν := by
  obtain ⟨G, hn, hlo, hhi, hw⟩ := exists_originalStageClockGrid
    (lo := D.lo + (S.level : ℝ)) (hi := D.hi + (S.level : ℝ))
    (by linarith [D.support.lt]) hδ
  have hμ : ∀ᵐ x ∂μ, x ∈ Ico (G.cut 0) (G.cut G.count) := by
    filter_upwards [D.support.source.ae_open] with x hx
    rw [hlo, hhi]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hν : ∀ᵐ x ∂ν, x ∈ Ioc (G.cut 0) (G.cut G.count) := by
    filter_upwards [D.support.target.ae_open] with x hx
    rw [hlo, hhi]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact ⟨G, hn, hlo, hhi, hw, (G.sum_restrict μ ν hμ hν).1, (G.sum_restrict μ ν hμ hν).2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
