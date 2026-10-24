import OTSelector.Probability.SubcouplingTypeMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationRNSubplanTypes.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationRNSubplanTypes`; the selected original proof blocks follow. -/
section

/-!
# Probability.RNSubplanTypeRefinement

## Lemma skeleton

* **Conditions:** Finite original fractional type components and a fixed subplan dominated by the original paired law; exact selected recovery additionally assumes the types sum to that law.
* **Objects:** RN-weighted selected/complement type refinement, component domination, unchanged total and exact selected subplan/mass.
* **Proof detail:** Multiply each original component by the subplan-to-parent RN derivative, which lies in [0,1] almost everywhere; keep its positive complement and distribute density multiplication over the finite type sum.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Fractional positive-measure refinement, requiring neither disjoint original type supports nor a new geometric partition.
-/

/-!
# A fixed original subplan refines every original population type

The original Radon--Nikodym factor restricts each type to its share of a prescribed
subplan. Its complementary share remains a type. This preserves all original mass
and applies even when the starting types are already fractional subpopulations.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y))

/-- The share of a prescribed original subplan carried by an existing type. -/
def rnSubplanComponent (t : T) : Measure (X × Y) :=
  (D.component t).withDensity (η.rnDeriv π)

/-- The original subplan factor is at most one on every original component. -/
theorem rnSubplanComponent_le (hη : η ≤ π) (t : T) :
    D.rnSubplanComponent η t ≤ D.component t := by
  have h := withDensity_mono (ae_mono (D.component_le t) (Measure.rnDeriv_le_one_of_le hη))
  simpa only [rnSubplanComponent, withDensity_one] using h

theorem rnSubplanComponent_isFinite (hη : η ≤ π) (t : T) :
    IsFiniteMeasure (D.rnSubplanComponent η t) :=
  isFiniteMeasure_of_le (D.component t) (D.rnSubplanComponent_le η hη t)

/-- Retained and complementary flags of an existing original population type. -/
def rnSplitComponent (t : Bool × T) : Measure (X × Y) :=
  if t.1 then D.rnSubplanComponent η t.2 else D.component t.2 - D.rnSubplanComponent η t.2

/-- Both flags reconstruct their original type exactly. -/
theorem rnSplitComponent_sum (hη : η ≤ π) :
    (∑ t, D.rnSplitComponent η t) = ∑ t, D.component t := by
  let _inst (t : T) : IsFiniteMeasure (D.rnSubplanComponent η t) :=
    D.rnSubplanComponent_isFinite η hη t
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [rnSplitComponent, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [add_comm, Measure.sub_add_cancel_of_le (D.rnSubplanComponent_le η hη t)]

/-- The refined type law keeps the full original coupling as its ambient measure. -/
def rnSubplanTypes (hη : η ≤ π) : PopulationSubcouplingTypes π (Bool × T) where
  component := D.rnSplitComponent η
  dominated := by rw [D.rnSplitComponent_sum η hη]; exact D.dominated

/-- Each refined type preserves every almost-everywhere property of its old type. -/
theorem rnSubplanTypes_component_le (hη : η ≤ π) (t : Bool × T) :
    (D.rnSubplanTypes η hη).component t ≤ D.component t.2 := by
  cases hb : t.1
  · exact (by simpa only [rnSubplanTypes, rnSplitComponent, hb, Bool.false_eq_true,
      ↓reduceIte] using (show D.component t.2 - D.rnSubplanComponent η t.2 ≤
        D.component t.2 from Measure.sub_le))
  · simpa only [rnSubplanTypes, rnSplitComponent, hb, ↓reduceIte] using
      D.rnSubplanComponent_le η hη t.2

/-- Full original mass remains full after the fixed subplan refinement. -/
theorem rnSubplanTypes_sum_eq (hη : η ≤ π) (hfull : ∑ t, D.component t = π) :
    (∑ t, (D.rnSubplanTypes η hη).component t) = π :=
  (D.rnSplitComponent_sum η hη).trans hfull

/-- All selected flags recover precisely the prescribed original subplan. -/
theorem rnSubplanTypes_selected_sum_eq (hη : η ≤ π) (hfull : ∑ t, D.component t = π) :
    (∑ t, (D.rnSubplanTypes η hη).component (true, t)) = η := by
  let _inst : IsFiniteMeasure η := isFiniteMeasure_of_le π hη
  change (∑ t, (D.component t).withDensity (η.rnDeriv π)) = η
  rw [← Measure.sum_fintype, ← withDensity_sum, Measure.sum_fintype, hfull]
  exact Measure.withDensity_rnDeriv_eq η π hη.absolutelyContinuous

/-- The selected original type masses sum to the prescribed subplan mass. -/
theorem rnSubplanTypes_selected_mass (hη : η ≤ π) (hfull : ∑ t, D.component t = π) :
    (∑ t, (D.rnSubplanTypes η hη).component (true, t) univ) = η univ := by
  rw [← Measure.finsetSum_apply, D.rnSubplanTypes_selected_sum_eq η hη hfull]

end OTSelector.Reconstruction.PopulationSubcouplingTypes

end
end
