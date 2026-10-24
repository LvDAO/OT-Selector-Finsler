import OTSelector.Finite.OrderedHallFlow
import OTSelector.Finite.ThresholdClockHallFlow
import OTSelector.Probability.ConditionalClockClassCoupling
import OTSelector.Probability.FiniteCellClassFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalClassFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalClassFlow`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawOriginalClassFlow

**Conditions:** Actual original common-label conditional coupling data and finite disjoint source/target clock bins covering their conditional marginals.

**Objects:** A measurable nonnegative legal finite class matrix with exact conditional masses, Hall cuts and total one.

**Proof detail:** Evaluate the actual conditional plan on the bin rectangles; finite disjoint additivity gives marginals and total mass, legal concentration gives forbidden zeros, and summing a source cut yields Hall inequalities.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [OTSelector project, Measurable forward weighted Hall construction](main.tex#measurable-forward-hall), main.tex label measurable-forward-hall, line 6889.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Actual original common-label conditional coupling data produce a measurable
legal finite class matrix, its exact original marginal masses, all Hall cuts
and its total mass. No finite feasibility premise is introduced.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An actual unchanged original common-label coupling supplies all original
finite clock-class feasibility data, including Hall, with no feasibility oracle.
The original conditional clock laws are kept literally. -/
theorem exists_original_feasible_clockClassFlow
    {X Z : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] {M L : ℕ}
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (δ : ℝ) (hgap : ∀ᵐ p ∂π, δ ≤ u p.2 - u p.1)
    (S : Fin M → Set ℝ) (T : Fin L → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : ∀ᵐ z ∂μ.map a, ∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ i, S i)
    (hcoverT : ∀ᵐ z ∂μ.map a, ∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ j, T j)
    (allowed : Fin M → Fin L → Prop)
    (hbins : ∀ i j, ∀ s ∈ S i, ∀ t ∈ T j, δ ≤ t - s → allowed i j) :
    ∃ γ : Kernel Z (ℝ × ℝ), IsMarkovKernel γ ∧ μ.map a = ν.map a ∧
      ∀ᵐ z ∂μ.map a,
        (∀ i j, 0 ≤ actualClockClassFlow (γ z) S T i j) ∧
        (∀ i, ∑ j, actualClockClassFlow (γ z) S T i j = (condDistrib u a μ z).real (S i)) ∧
        (∀ j, ∑ i, actualClockClassFlow (γ z) S T i j = (condDistrib u a ν z).real (T j)) ∧
        (∀ i j, ¬ allowed i j → actualClockClassFlow (γ z) S T i j = 0) ∧
        (∀ A : Finset (Fin M), (∑ i ∈ A, (condDistrib u a μ z).real (S i)) ≤
          ∑ j ∈ orderedClockNeighbors allowed A, (condDistrib u a ν z).real (T j)) ∧
        (∑ i, ∑ j, actualClockClassFlow (γ z) S T i j) = 1 := by
  obtain ⟨γ, hγ, hbalance, _, _, hcoupling⟩ :=
    exists_original_clockPair_kernel μ ν π hπ a u ha hu hlabel δ hgap
  let _instMarkov : IsMarkovKernel γ := hγ
  refine ⟨γ, hγ, hbalance, ?_⟩
  filter_upwards [hcoupling, hcoverS, hcoverT] with z hz hs ht
  have hsγ : ∀ᵐ p ∂γ z, p.1 ∈ ⋃ i, S i :=
    ae_of_ae_map measurable_fst.aemeasurable (hz.1.1.symm ▸ hs)
  have htγ : ∀ᵐ p ∂γ z, p.2 ∈ ⋃ j, T j :=
    ae_of_ae_map measurable_snd.aemeasurable (hz.1.2.symm ▸ ht)
  have hrow (i : Fin M) : (∑ j, actualClockClassFlow (γ z) S T i j) =
      (condDistrib u a μ z).real (S i) := by
    rw [actualClockClassFlow_row (γ z) S T hS hT hdT htγ i, hz.1.1]
  have hcol (j : Fin L) : (∑ i, actualClockClassFlow (γ z) S T i j) =
      (condDistrib u a ν z).real (T j) := by
    rw [actualClockClassFlow_col (γ z) S T hS hT hdS hsγ j, hz.1.2]
  have hzero (i : Fin M) (j : Fin L) (hnot : ¬ allowed i j) :
      actualClockClassFlow (γ z) S T i j = 0 :=
    actualClockClassFlow_zero (γ z) S T allowed (fun p ↦ δ ≤ p.2 - p.1) hz.2
      (fun i j p hi hj hp ↦ hbins i j p.1 hi p.2 hj hp) i j hnot
  refine ⟨actualClockClassFlow_nonneg _ _ _, hrow, hcol, hzero, ?_, ?_⟩
  · intro A
    exact finiteClockFlow_hall allowed (actualClockClassFlow (γ z) S T) _ _
      (actualClockClassFlow_nonneg _ _ _) hrow hcol hzero A
  · simp_rw [hrow]
    rw [← measureReal_iUnion_fintype hdS hS]
    have he : (condDistrib u a μ z).real (⋃ i, S i) = (condDistrib u a μ z).real univ := by
      apply measureReal_congr
      filter_upwards [hs] with s hs
      apply propext
      change (s ∈ ⋃ i, S i) ↔ s ∈ (univ : Set ℝ)
      exact iff_of_true hs (mem_univ s)
    rw [he]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]

end OTSelector.Reconstruction

end
end
