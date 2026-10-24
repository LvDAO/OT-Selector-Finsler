import OTSelector.Transport.Calibration.CompactClockGap
import OTSelector.Reconstruction.PopulationScalarBinTypes

/-!
# Actual scalar-bin types from the original calibrated Finsler coupling

Disjoint compact physical carriers produce a positive clock gap for the same
calibrated population coupling. The existing finite scalar-bin construction
then retains its full mass. No realized sample balance or extra geometric
condition is supplied.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] {F : ContinuousFinslerNorm E M}

/-- The same original calibrated coupling supplies its own positive scalar gap
and a finite full-mass type decomposition. Positive types admit every pair of
their source and target clock bins, with half the original gap. -/
theorem exists_finsler_original_legal_scalar_types
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) {u : M → ℝ}
    (hu : let _instOriginalLegalTypesMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hcal : ∀ᵐ p ∂π, (F.lengthEDist p.1 p.2).toReal = u p.2 - u p.1) :
    let _instOriginalLegalTypesConclusionMetric : MetricSpace M := F.metricSpace
    ∃ gap : ℝ, 0 < gap ∧ (∀ᵐ p ∂π, gap ≤ u p.2 - u p.1) ∧
      ∃ bins : FiniteScalarBins (u '' A ∪ u '' B) gap,
        (let types := scalarBinPopulationTypes bins (fun _ : M × M ↦ ()) u u π
          measurable_const hu.continuous.measurable hu.continuous.measurable
         (∑ t, types.component t) = π ∧
           ∀ t : Unit × Fin bins.count × Fin bins.count,
             types.component t univ ≠ 0 →
             ∀ s ∈ bins.cell t.2.1, ∀ r ∈ bins.cell t.2.2, gap / 2 ≤ r - s) := by
  let _instOriginalLegalTypesProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨gap, hgap, hdist⟩ := exists_original_support_gap hA hB hAB
  have hsource : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ.1]; exact hμ)
  have htarget : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hπ.2]; exact hν)
  have hclock : ∀ᵐ p ∂π, gap ≤ u p.2 - u p.1 := by
    filter_upwards [hsource, htarget, hcal] with p hs ht hc
    have h := hdist p.1 hs p.2 ht
    rwa [F.metricSpace_dist, hc] at h
  obtain ⟨bins, hfull, hseparated⟩ := exists_scalarBinPopulationTypes_of_compact_support
    (chart := fun _ : M × M ↦ ()) (source := u) (target := u) (δ := gap)
    hA hB π hπ hμ hν measurable_const hu.continuous hu.continuous hgap hclock
  exact ⟨gap, hgap, hclock, bins, hfull, hseparated⟩

end OTSelector.Reconstruction
