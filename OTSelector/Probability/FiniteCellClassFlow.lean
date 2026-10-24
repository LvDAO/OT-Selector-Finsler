import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.WithDensity
import OTSelector.Finite.OrderedHallFlow
import OTSelector.Finite.ThresholdClockHallFlow
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawActualClockClassFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawActualClockClassFlow`; the selected original proof blocks follow. -/
section

/-!
# Probability.FiniteCellClassFlow

## Lemma skeleton

* **Conditions:** A finite actual coupling and finite measurable disjoint source/target bins covering it almost everywhere; a given legal relation implies a finite allowed graph.
* **Objects:** Measurable nonnegative cell-flow weights, exact row/column/total masses and weighted Hall inequalities.
* **Proof detail:** Define each weight as real rectangle mass. Sum the finite disjoint partition for marginals, set forbidden weights to zero using legal carrying and sum feasible nonnegative flow into the neighbor bins for Hall.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): An existing coupling supplies a feasible flow and hence necessary Hall inequalities; no converse matching existence is claimed here.
-/

/-!
The actual original continuous clock-pair law yields measurable finite class weights, exact original marginals and weighted Hall feasibility.
-/

open MeasureTheory Function Set ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Actual original continuous clock-pair mass in a finite class rectangle. -/
def actualClockClassFlow {I J X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) (S : I → Set X) (T : J → Set Y) (i : I) (j : J) : ℝ :=
  γ.real (S i ×ˢ T j)

theorem actualClockClassFlow_nonneg {I J X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) (S : I → Set X) (T : J → Set Y) (i : I) (j : J) :
    0 ≤ actualClockClassFlow γ S T i j := measureReal_nonneg

/-- Rows of the actual original class coupling are the unchanged original
source-bin masses, including target classes of zero mass. -/
theorem actualClockClassFlow_row
    {I J X Y : Type*} [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) [IsFiniteMeasure γ]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hd : Pairwise (Disjoint on T)) (hcover : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, T j) (i : I) :
    (∑ j, actualClockClassFlow γ S T i j) = (γ.map Prod.fst).real (S i) := by
  have hdis : Pairwise (Disjoint on fun j ↦ S i ×ˢ T j) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro p hp hq
    exact disjoint_left.mp (hd hjk) hp.2 hq.2
  have hset : (⋃ j, S i ×ˢ T j) = S i ×ˢ ⋃ j, T j := by
    ext p
    simp only [mem_iUnion, mem_prod]
    aesop
  calc
    _ = γ.real (⋃ j, S i ×ˢ T j) :=
      (measureReal_iUnion_fintype hdis (fun j ↦ (hS i).prod (hT j))).symm
    _ = γ.real (S i ×ˢ ⋃ j, T j) := by rw [hset]
    _ = γ.real (Prod.fst ⁻¹' S i) := by
      apply measureReal_congr
      filter_upwards [hcover] with p hp
      apply propext
      change (p.1 ∈ S i ∧ p.2 ∈ ⋃ j, T j) ↔ p.1 ∈ S i
      exact and_iff_left hp
    _ = _ := (map_measureReal_apply measurable_fst (hS i)).symm

/-- Column sums recover the unchanged original target-bin masses. -/
theorem actualClockClassFlow_col
    {I J X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) [IsFiniteMeasure γ]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hd : Pairwise (Disjoint on S)) (hcover : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, S i) (j : J) :
    (∑ i, actualClockClassFlow γ S T i j) = (γ.map Prod.snd).real (T j) := by
  have hdis : Pairwise (Disjoint on fun i ↦ S i ×ˢ T j) := by
    intro i k hik
    apply disjoint_left.mpr
    intro p hp hq
    exact disjoint_left.mp (hd hik) hp.1 hq.1
  have hset : (⋃ i, S i ×ˢ T j) = (⋃ i, S i) ×ˢ T j := by
    ext p
    simp only [mem_iUnion, mem_prod]
    aesop
  calc
    _ = γ.real (⋃ i, S i ×ˢ T j) :=
      (measureReal_iUnion_fintype hdis (fun i ↦ (hS i).prod (hT j))).symm
    _ = γ.real ((⋃ i, S i) ×ˢ T j) := by rw [hset]
    _ = γ.real (Prod.snd ⁻¹' T j) := by
      apply measureReal_congr
      filter_upwards [hcover] with p hp
      apply propext
      change (p.1 ∈ ⋃ i, S i) ∧ p.2 ∈ T j ↔ p.2 ∈ T j
      exact and_iff_right hp
    _ = _ := (map_measureReal_apply measurable_snd (hT j)).symm

/-- Original calibrated support forces forbidden class-rectangle flow to zero. -/
theorem actualClockClassFlow_zero
    {I J X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) (S : I → Set X) (T : J → Set Y)
    (allowed : I → J → Prop) (legal : X × Y → Prop)
    (hlegal : ∀ᵐ p ∂γ, legal p)
    (hbins : ∀ i j, ∀ p : X × Y, p.1 ∈ S i → p.2 ∈ T j → legal p → allowed i j)
    (i : I) (j : J) (hnot : ¬ allowed i j) : actualClockClassFlow γ S T i j = 0 := by
  unfold actualClockClassFlow
  have hnull : γ (S i ×ˢ T j) = 0 := by
    apply measure_mono_null (fun p hp ↦ ?_) (ae_iff.mp hlegal)
    intro hl
    exact hnot (hbins i j p hp.1 hp.2 hl)
  simp only [measureReal_def, hnull, ENNReal.toReal_zero]

/-- These weights are actual measurable functions of the original conditional
coupling kernel. No residual selection or independence is introduced. -/
theorem measurable_actualClockClassFlow
    {I J Z X Y : Type*} [MeasurableSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Kernel Z (X × Y)) (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (i : I) (j : J) : Measurable (fun z ↦ actualClockClassFlow (γ z) S T i j) :=
  (γ.measurable_coe ((hS i).prod (hT j))).ennreal_toReal

/-- The literal original conditional clock-pair law proves feasibility of the
weighted finite class masses. The root-density factor is kept exactly. -/
theorem actualClockClassFlow_hall
    {M L : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) [IsFiniteMeasure γ]
    (S : Fin M → Set X) (T : Fin L → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : ∀ᵐ p ∂γ, p.1 ∈ ⋃ i, S i) (hcoverT : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, T j)
    (allowed : Fin M → Fin L → Prop) (legal : X × Y → Prop)
    (hlegal : ∀ᵐ p ∂γ, legal p)
    (hbins : ∀ i j, ∀ p : X × Y, p.1 ∈ S i → p.2 ∈ T j → legal p → allowed i j)
    (d : ℝ) (hd : 0 ≤ d) (A : Finset (Fin M)) :
    (∑ i ∈ A, d * (γ.map Prod.fst).real (S i)) ≤
      ∑ j ∈ orderedClockNeighbors allowed A, d * (γ.map Prod.snd).real (T j) := by
  apply finiteClockFlow_hall allowed (fun i j ↦ d * actualClockClassFlow γ S T i j)
  · intro i j
    exact mul_nonneg hd (actualClockClassFlow_nonneg γ S T i j)
  · intro i
    rw [← Finset.mul_sum, actualClockClassFlow_row γ S T hS hT hdT hcoverT i]
  · intro j
    rw [← Finset.mul_sum, actualClockClassFlow_col γ S T hS hT hdS hcoverS j]
  · intro i j hij
    rw [actualClockClassFlow_zero γ S T allowed legal hlegal hbins i j hij, mul_zero]

/-- A total finite clock partition retains the original conditional total mass. -/
theorem actualClockClassFlow_total
    {I J X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace Y]
    (γ : Measure (X × Y)) [IsFiniteMeasure γ]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : (⋃ i, S i) = univ) (hcoverT : (⋃ j, T j) = univ) :
    (∑ i, ∑ j, actualClockClassFlow γ S T i j) = γ.real univ := by
  have hcover : ∀ᵐ p ∂γ, p.2 ∈ ⋃ j, T j := Filter.Eventually.of_forall fun p ↦ by rw [hcoverT]; exact mem_univ _
  simp_rw [actualClockClassFlow_row γ S T hS hT hdT hcover]
  rw [← measureReal_iUnion_fintype hdS hS, hcoverS,
    map_measureReal_apply measurable_fst MeasurableSet.univ, preimage_univ]

end OTSelector.Reconstruction

end
end
