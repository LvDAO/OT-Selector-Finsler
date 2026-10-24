import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneLimitMarginalMeasurability.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneLimitMarginalMeasurability`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.MarginalLocalFinitenessMeasurability

## Lemma skeleton

* **Conditions:** A genuine compact exhaustion of either coordinate in the inherited locally compact vague product-measure carrier.
* **Objects:** Borel events expressing local finiteness of the full first or second marginal.
* **Proof detail:** A projection is finite on compact sets exactly when all exhaustion-interior rectangle masses are finite. These evaluations are measurable/lower semicontinuous, so take a countable intersection.

## Mathematical sources

- [Olav Kallenberg, Random Measures, Theory and Applications (Springer 2017)](https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4): Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (composition): Measurability of a nonproper projected local-finiteness predicate from countably many actual windows.
-/

/-!
# Measurability of full marginal local finiteness

A genuine compact exhaustion detects local finiteness of the full nonproper
projection through countably many open rectangles in the actual vague carrier.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [LocallyCompactSpace Y] [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
  [SecondCountableTopology Y]

/-- Full source local finiteness is a measurable property of the actual vague
plan, despite the source projection being nonproper. -/
theorem measurableSet_physicalScene_fst_locallyFinite (K : CompactExhaustion X) :
    MeasurableSet {π : LocalFiniteMeasure (X × Y) |
      IsFiniteMeasureOnCompacts (π : Measure (X × Y)).fst} := by
  have heq : {π : LocalFiniteMeasure (X × Y) |
      IsFiniteMeasureOnCompacts (π : Measure (X × Y)).fst} =
      {π : LocalFiniteMeasure (X × Y) | ∀ n, (π : Measure (X × Y))
        (interior (K n) ×ˢ univ) < ⊤} := by
    ext π
    constructor
    · intro h n
      let _ : IsFiniteMeasureOnCompacts (π : Measure (X × Y)).fst := h
      have hfin : (π : Measure (X × Y)).fst (K n) < ⊤ := (K.isCompact n).measure_lt_top
      rw [Measure.fst, Measure.map_apply measurable_fst (K.isCompact n).measurableSet] at hfin
      exact (measure_mono (show interior (K n) ×ˢ (univ : Set Y) ⊆ Prod.fst ⁻¹' K n from
        fun e he ↦ (interior_subset : interior (K n) ⊆ K n) he.1)).trans_lt hfin
    · intro h
      constructor
      intro L hL
      obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hL
      rw [Measure.fst, Measure.map_apply measurable_fst hL.measurableSet]
      exact (measure_mono (show Prod.fst ⁻¹' L ⊆ interior (K (n + 1)) ×ˢ (univ : Set Y) from
        fun e he ↦ ⟨K.subset_interior_succ n (hn he), mem_univ _⟩)).trans_lt (h (n + 1))
  rw [heq]
  simpa only [Set.ofPred_forall] using MeasurableSet.iInter fun n : ℕ ↦ measurableSet_lt
    (LocalFiniteMeasure.measurable_measure_open ((isOpen_interior (s := K n)).prod isOpen_univ))
      (measurable_const : Measurable (fun _ : LocalFiniteMeasure (X × Y) ↦ (⊤ : ℝ≥0∞)))

/-- The corresponding target property is also measurable on the actual vague
plan carrier. -/
theorem measurableSet_physicalScene_snd_locallyFinite (K : CompactExhaustion Y) :
    MeasurableSet {π : LocalFiniteMeasure (X × Y) |
      IsFiniteMeasureOnCompacts (π : Measure (X × Y)).snd} := by
  have heq : {π : LocalFiniteMeasure (X × Y) |
      IsFiniteMeasureOnCompacts (π : Measure (X × Y)).snd} =
      {π : LocalFiniteMeasure (X × Y) | ∀ n, (π : Measure (X × Y))
        (univ ×ˢ interior (K n)) < ⊤} := by
    ext π
    constructor
    · intro h n
      let _ : IsFiniteMeasureOnCompacts (π : Measure (X × Y)).snd := h
      have hfin : (π : Measure (X × Y)).snd (K n) < ⊤ := (K.isCompact n).measure_lt_top
      rw [Measure.snd, Measure.map_apply measurable_snd (K.isCompact n).measurableSet] at hfin
      exact (measure_mono (show (univ : Set X) ×ˢ interior (K n) ⊆ Prod.snd ⁻¹' K n from
        fun e he ↦ (interior_subset : interior (K n) ⊆ K n) he.2)).trans_lt hfin
    · intro h
      constructor
      intro L hL
      obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hL
      rw [Measure.snd, Measure.map_apply measurable_snd hL.measurableSet]
      exact (measure_mono (show Prod.snd ⁻¹' L ⊆ (univ : Set X) ×ˢ interior (K (n + 1)) from
        fun e he ↦ ⟨mem_univ _, K.subset_interior_succ n (hn he)⟩)).trans_lt (h (n + 1))
  rw [heq]
  simpa only [Set.ofPred_forall] using MeasurableSet.iInter fun n : ℕ ↦ measurableSet_lt
    (LocalFiniteMeasure.measurable_measure_open (isOpen_univ.prod (isOpen_interior (s := K n))))
      (measurable_const : Measurable (fun _ : LocalFiniteMeasure (X × Y) ↦ (⊤ : ℝ≥0∞)))

end OTSelector.Reconstruction

end
end
