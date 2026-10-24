import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowCore
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMeasureLaw

/-!
# Original finite colors under exact stationary-window identification

Taking an immutable original color commutes with an actual physical-window
restriction. Reading the same finite two-color array recovers exactly its
original source and target counting measures.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A color readout on a measurable physical set is its unchanged tagged set. -/
theorem legalInputColorMeasure_apply_prod (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    {V : Set (LegalMarkedPhysicalPoint q)} (hV : MeasurableSet V) :
    legalInputColorMeasure q μ c V = (μ : Measure (LegalColoredInputPoint q)) (V ×ˢ {c}) := by
  rw [legalInputColorMeasure, Measure.map_apply measurable_fst hV,
    Measure.restrict_apply (hV.preimage measurable_fst)]
  congr 1

/-- Restriction leaves the original source or target color unchanged. -/
theorem legalInputColorMeasure_restrict_prod (q : ℕ)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U) :
    legalInputColorMeasure q (legalInputRestrictionLocal (U ×ˢ univ) μ) c =
      (legalInputColorMeasure q μ c).restrict U := by
  apply Measure.ext
  intro V hV
  rw [legalInputColorMeasure_apply_prod q _ c hV, Measure.restrict_apply hV,
    legalInputColorMeasure_apply_prod q μ c (hV.inter hU)]
  change (μ : Measure (LegalColoredInputPoint q)).restrict (U ×ˢ univ) (V ×ˢ {c}) = _
  rw [Measure.restrict_apply (hV.prod (measurableSet_singleton c))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
  tauto

/-- The zero color of the literal two original finite arrays is exactly the
original source array, with its actual finite multiplicities retained. -/
theorem legalInputColorMeasure_twoBlock_source (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputColorMeasure q (legalInputTwoBlockLocal q b) 0 = legalInputBlockMeasure b.1 := by
  apply Measure.ext
  intro V hV
  rw [legalInputColorMeasure_apply_prod q _ 0 hV]
  simp only [legalInputTwoBlockLocal, legalInputTwoBlockMeasure, legalInputBlockMeasure,
    mapBlockData, Measure.add_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ (hV.prod (measurableSet_singleton (0 : Fin 2))),
    Measure.dirac_apply' _ hV]
  simp
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hx : b.1.2 i ∈ V <;> simp [hx]

/-- The one color recovers the same original target array. -/
theorem legalInputColorMeasure_twoBlock_target (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputColorMeasure q (legalInputTwoBlockLocal q b) 1 = legalInputBlockMeasure b.2 := by
  apply Measure.ext
  intro V hV
  rw [legalInputColorMeasure_apply_prod q _ 1 hV]
  simp only [legalInputTwoBlockLocal, legalInputTwoBlockMeasure, legalInputBlockMeasure,
    mapBlockData, Measure.add_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ (hV.prod (measurableSet_singleton (1 : Fin 2))),
    Measure.dirac_apply' _ hV]
  simp
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hy : b.2.2 j ∈ V <;> simp [hy]

/-- Equality of the same tagged window readouts identifies both entire
original endpoint restrictions of a genuine matching with the original arrays.
No selected-endpoint distribution is used. -/
theorem original_window_marginals_eq_of_colored_readout (q : ℕ)
    (s : LegalMarkedOptimalInputScene q) (hs : IsFullOriginalInputMatching q s)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    (hread : legalInputRestrictionLocal (U ×ˢ univ) s.2 =
      legalInputRestrictionLocal (U ×ˢ univ) (legalInputTwoBlockLocal q b)) :
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst.restrict U =
        (legalInputBlockMeasure b.1).restrict U ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd.restrict U =
        (legalInputBlockMeasure b.2).restrict U := by
  have hsource := congrArg (fun ν ↦ legalInputColorMeasure q ν 0) hread
  have htarget := congrArg (fun ν ↦ legalInputColorMeasure q ν 1) hread
  rw [legalInputColorMeasure_restrict_prod q s.2 0 hU,
    legalInputColorMeasure_restrict_prod q (legalInputTwoBlockLocal q b) 0 hU,
    legalInputColorMeasure_twoBlock_source] at hsource
  rw [legalInputColorMeasure_restrict_prod q s.2 1 hU,
    legalInputColorMeasure_restrict_prod q (legalInputTwoBlockLocal q b) 1 hU,
    legalInputColorMeasure_twoBlock_target] at htarget
  exact ⟨(congrArg (fun μ ↦ μ.restrict U) hs.source_marginal).trans hsource,
    (congrArg (fun μ ↦ μ.restrict U) hs.target_marginal).trans htarget⟩

end OTSelector.Reconstruction
