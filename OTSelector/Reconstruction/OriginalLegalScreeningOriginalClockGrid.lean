import OTSelector.Reconstruction.OriginalStageClockSlabsWidth
import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClockSlabBlocksFlow

/-! The genuine conditional support and actual forward coupling produce the complete clock grid. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators ContDiff Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- An actual forward coupling supplies one genuine short original clock grid
with its exact outer cuts, separate Ico/Ioc covers, monochrome cells, zero
surplus endpoints, nonnegative prefixes and both exact law decompositions.
No grid, strict Hall condition or completed surplus certificate is assumed. -/
theorem exists_originalLegalScreeningClockGrid {gap diameter : ℝ}
    (hgap : 0 < gap) (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π μ ν)
    (horder : ∀ᵐ p ∂π, p.1 ≤ p.2) :
    ∃ G : OriginalStageClockGrid, 0 < G.count ∧
      G.cut 0 = D.lo+(S.level : ℝ) ∧ G.cut G.count = D.hi+(S.level : ℝ) ∧
      (∀ i : Fin G.count, G.cut (i+1)-G.cut i < gap) ∧
      (∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i) ∧
      (∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i) ∧
      (∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0) ∧
      G.clockSlabSurplus μ ν 0 = 0 ∧ G.clockSlabSurplus μ ν G.count = 0 ∧
      (∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus μ ν k) ∧
      (∑ i, μ.restrict (G.sourceCell i)) = μ ∧
      (∑ i, ν.restrict (G.targetCell i)) = ν := by
  have : IsProbabilityMeasure (π.map Prod.fst) := by
    rw [hπ.1]
    exact D.support.source.probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  obtain ⟨G,hcount,hlo,hhi,hwidth,hsumS,hsumT⟩ := D.exists_originalShortClockSlabGrid hgap hbounds
  have hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i := by
    rw [G.source_union,hlo,hhi]
    filter_upwards [D.support.source.ae_open] with x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have ht : ∀ᵐ y ∂ν, y ∈ ⋃ i, G.targetCell i := by
    rw [G.target_union,hlo,hhi]
    filter_upwards [D.support.target.ae_open] with y hy
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0 :=
    fun i ↦ originalClockHalfOpenSlab_monochrome hbounds (hwidth i)
  obtain ⟨hzero,hend,hprefix⟩ := G.clockSlabSurplus_facts hgap hbounds π hπ hs ht hmono horder
  exact ⟨G,hcount,hlo,hhi,hwidth,hs,ht,hmono,hzero,hend,hprefix,hsumS,hsumT⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
