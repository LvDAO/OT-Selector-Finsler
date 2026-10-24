import OTSelector.Finite.AtomicIndexEquivalence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairOriginalAtomFamilies.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairOriginalAtomFamilies`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairOriginalAtomFamilies

**Conditions:** Two finite labelled arrays have equal counting measures and given probability smoothing laws with integrable endpoint deviations.

**Objects:** Smoothing families transferred to the unchanged original labels with exact energy and clock-class laws.

**Proof detail:** Use equality of counting laws to obtain a point-preserving index equivalence, transport each smoothing law along it and reindex all integrals and class-indicator sums.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22), Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Transfer genuine endpoint smoothing families to the unchanged original labels. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- An exact original counting-measure identity transfers real port/reserve
smoothing laws to the unchanged unused labels. It preserves every clock class
and the total actual Euclidean deviation energy, including repeated values
and empty families. The family is constructed by value-preserving relabeling. -/
theorem exists_originalAtomFamily_of_countingMeasure_eq
    {X E I J : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype I] [Fintype J] [PseudoMetricSpace E] [MeasurableSpace E]
    (x : I → X) (y : J → X)
    (hxy : (∑ i, Measure.dirac (x i)) = ∑ j, Measure.dirac (y j))
    (position : X → E) (clock : X → ℝ) (laws : J → Measure E)
    (hlaws : ∀ j, IsProbabilityMeasure (laws j))
    (hI : ∀ j, Integrable (fun v ↦ dist (position (y j)) v^2) (laws j)) :
    ∃ κ : I → Measure E,
      (∀ i, IsProbabilityMeasure (κ i)) ∧
      (∀ i, Integrable (fun v ↦ dist (position (x i)) v^2) (κ i)) ∧
      (∑ i, ∫ v, dist (position (x i)) v^2 ∂κ i) =
        ∑ j, ∫ v, dist (position (y j)) v^2 ∂laws j ∧
      ∀ C : Set ℝ, (∑ i, if clock (x i) ∈ C then κ i else 0) =
        ∑ j, if clock (y j) ∈ C then laws j else 0 := by
  obtain ⟨e,he⟩ := exists_originalIndexEquiv_of_sum_dirac_eq x y hxy
  have hs := originalAtomFamily_pullback_spec x y e he position clock laws hlaws
  exact ⟨fun i ↦ laws (e i),hs.1,hs.2.2.2.2.mpr hI,hs.2.2.1,hs.2.2.2.1⟩

end OTSelector.Reconstruction

end
end
