import OTSelector.Reconstruction.OriginalStageClockSlabsProducer
import OTSelector.Reconstruction.FinslerOriginalConditionalMoments

/-! The actual original conditional clock span produces its finite analytic stages. -/
open Set Function MeasureTheory Module Manifold
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
/-- The same original conditional laws, support endpoints and gap internally supply a
finite genuine clock-slab grid with the exact analytic source and target conventions. -/
theorem exists_originalMonochromeClockSlabGrid {δ diameter : ℝ}
    (hδ : 0 < δ) (hsep : ConditionalClockSupportBounds μ ν δ diameter) :
    ∃ G : OriginalStageClockGrid, 0 < G.count ∧
      G.cut 0 = D.lo + (S.level : ℝ) ∧ G.cut G.count = D.hi + (S.level : ℝ) ∧
      (∑ i, μ.restrict (G.sourceCell i)) = μ ∧
      (∑ i, ν.restrict (G.targetCell i)) = ν ∧
      ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0 := by
  have hμ : ∀ᵐ x ∂μ, x ∈ Ioo (D.lo + (S.level : ℝ)) (D.hi + (S.level : ℝ)) := by
    filter_upwards [D.support.source.ae_open] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hν : ∀ᵐ x ∂ν, x ∈ Ioo (D.lo + (S.level : ℝ)) (D.hi + (S.level : ℝ)) := by
    filter_upwards [D.support.target.ae_open] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact exists_originalMonochromeClockSlabs hsep hδ (by linarith [D.support.lt]) hμ hν

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
