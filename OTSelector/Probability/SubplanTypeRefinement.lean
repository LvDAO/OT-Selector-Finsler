import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Probability.SubcouplingTypeMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationSubplanTypes.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationSubplanTypes`; the selected original proof blocks follow. -/
section

/-!
# Probability.SubplanTypeRefinement

## Lemma skeleton

* **Conditions:** A finite measurable disjoint chart-bin family and a prescribed subplan dominated by the original coupling.
* **Objects:** Boolean retained/complement type refinement with exact total, selected mass, per-cell domination and inherited almost-everywhere facts.
* **Proof detail:** Restrict the prescribed subplan and its positive measure complement to each original type cell, sum the finite partition and transfer null facts by domination.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (composition): Explicit positive-measure refinement preserving the original ambient coupling; no geometric type choice is introduced.
-/

/-!
# Fixed original subplans refine actual population types

A prescribed subplan dominated by the original population coupling splits each
actual measurable chart-bin cell into retained and complementary subpopulations.
The ambient pairing stays the original coupling, the sum remains exact, and the
selected type mass is exactly the prescribed subplan mass.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  (π η : Measure (X × Y)) [IsFiniteMeasure η]
  (A : T → Set (X × Y)) (hA : ∀ t, MeasurableSet (A t))
  (hdis : Pairwise (fun s t ↦ Disjoint (A s) (A t)))

include hA hdis in
/-- The finite restriction sum is the unchanged measure on the actual cell union. -/
theorem sum_restrict_population_type_cells (ρ : Measure (X × Y)) :
    (∑ t, ρ.restrict (A t)) = ρ.restrict (⋃ t, A t) := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdis hA]

/-- A Boolean flag keeps membership in a fixed original subplan distinct from
its complement, within the same actual type cell. -/
def populationSubplanTypeComponent (t : Bool × T) : Measure (X × Y) :=
  if t.1 then η.restrict (A t.2) else (π - η).restrict (A t.2)

include hA hdis in
/-- The flagged components recover the original coupling on the same cell union. -/
theorem sum_populationSubplanTypeComponent (hη : η ≤ π) :
    (∑ t, populationSubplanTypeComponent π η A t) = π.restrict (⋃ t, A t) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [populationSubplanTypeComponent, Bool.false_eq_true,
    ↓reduceIte]
  rw [sum_restrict_population_type_cells A hA hdis,
    sum_restrict_population_type_cells A hA hdis, ← Measure.restrict_add,
    add_comm η, Measure.sub_add_cancel_of_le hη]

/-- The marked refinement is still a family of subcouplings of the full original
population law, even when the selected subplan has arbitrarily small mass. -/
def populationSubplanTypes (hη : η ≤ π) : PopulationSubcouplingTypes π (Bool × T) where
  component := populationSubplanTypeComponent π η A
  dominated := by
    rw [sum_populationSubplanTypeComponent π η A hA hdis hη]
    exact Measure.restrict_le_self

/-- Full original cell coverage gives exact full-population type decomposition. -/
theorem populationSubplanTypes_sum_eq (hη : η ≤ π)
    (hfull : ∀ᵐ p ∂π, p ∈ ⋃ t, A t) :
    (∑ t, (populationSubplanTypes π η A hA hdis hη).component t) = π := by
  exact (sum_populationSubplanTypeComponent π η A hA hdis hη).trans
    (Measure.restrict_eq_self_of_ae_mem hfull)

/-- Every refined type is dominated by its original actual chart-bin cell. -/
theorem populationSubplanTypes_component_le (hη : η ≤ π) (t : Bool × T) :
    (populationSubplanTypes π η A hA hdis hη).component t ≤ π.restrict (A t.2) := by
  change populationSubplanTypeComponent π η A t ≤ _
  cases hb : t.1
  · simpa only [populationSubplanTypeComponent, hb, Bool.false_eq_true, ↓reduceIte] using
      (Measure.restrict_mono (Subset.refl (A t.2)) (show π - η ≤ π from Measure.sub_le))
  · simpa only [populationSubplanTypeComponent, hb, ↓reduceIte] using
      (Measure.restrict_mono (Subset.refl (A t.2)) hη)

/-- The selected Boolean types reconstruct the prescribed subplan, with no
normalization or replacement of the original population coupling. -/
theorem populationSubplanTypes_selected_sum_eq (hη : η ≤ π)
    (hfull : ∀ᵐ p ∂π, p ∈ ⋃ t, A t) :
    (∑ t, (populationSubplanTypes π η A hA hdis hη).component (true, t)) = η := by
  change (∑ t, η.restrict (A t)) = η
  rw [sum_restrict_population_type_cells A hA hdis]
  exact Measure.restrict_eq_self_of_ae_mem (ae_mono hη hfull)

/-- The total selected original type mass equals the fixed subplan mass exactly. -/
theorem populationSubplanTypes_selected_mass (hη : η ≤ π)
    (hfull : ∀ᵐ p ∂π, p ∈ ⋃ t, A t) :
    (∑ t, (populationSubplanTypes π η A hA hdis hη).component (true, t) univ) = η univ := by
  rw [← Measure.finsetSum_apply,
    populationSubplanTypes_selected_sum_eq π η A hA hdis hη hfull]

/-- Every original typewise almost-everywhere property passes to both fixed
subplan flags, before any iid sample or matching is chosen. -/
theorem populationSubplanTypes_ae_of_original (hη : η ≤ π)
    (Good : T → X × Y → Prop) (hgood : ∀ t, ∀ᵐ p ∂π.restrict (A t), Good t p)
    (t : Bool × T) :
    ∀ᵐ p ∂(populationSubplanTypes π η A hA hdis hη).component t, Good t.2 p :=
  ae_mono (populationSubplanTypes_component_le π η A hA hdis hη t) (hgood t.2)

end OTSelector.Reconstruction

end
end
