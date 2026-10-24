import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OTSelector.Probability.CellRefinedMarkComponents
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalFinePhysicalGraph.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalFinePhysicalGraph`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawOriginalFinePhysicalGraph

**Conditions:** Finite original sample arrays and measurable actual endpoint legality for each physical class.

**Objects:** The canonical legal edge finset on unchanged fine indices and measurable equality events.

**Proof detail:** Test all finitely many candidate pairs using their original points and tags; finite intersections of measurable membership events identify each graph-equality fiber.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Measurable original endpoint relations define canonical graphs on unchanged fine indices. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An original physical legality relation is evaluated on the original sample indices. -/
def originalFinePhysicalGraph {X C T : Type*} {n : ℕ} (legal : C → X → X → Prop)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) (c : C) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e ↦ legal c (sample.1 e.1).1 (sample.2 e.2).1)

/-- A measurable original relation gives the exact finite graph fiber events;
no measurability of a subsequently selected matching is needed. -/
theorem measurableSet_originalFinePhysicalGraph_eq
    {X C T : Type*} [MeasurableSpace X] [Fintype C] [Fintype T]
    [MeasurableSpace (Option (CellRefinedType C T))] {n : ℕ}
    (legal : C → X → X → Prop)
    (hlegal : ∀ c, MeasurableSet {p : X × X | legal c p.1 p.2})
    (c : C) (S : Finset (Fin n × Fin n)) :
    MeasurableSet {sample | originalFinePhysicalGraph (T := T) (n := n) legal sample c = S} := by
  have hm : Measurable (fun sample ↦ originalFinePhysicalGraph (T := T) (n := n) legal sample c) := by
    apply measurable_finset_iff.mpr
    intro e
    apply measurableSet_setOfPred.mp
    have heq : {sample | e ∈ originalFinePhysicalGraph (T := T) (n := n) legal sample c} =
        {sample | legal c (sample.1 e.1).1 (sample.2 e.2).1} := by
      ext sample
      simp only [originalFinePhysicalGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact (hlegal c).preimage (show Measurable (fun sample :
      (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → X × Option (CellRefinedType C T)) ↦
          ((sample.1 e.1).1, (sample.2 e.2).1)) by fun_prop)
  exact (measurableSet_singleton S).preimage hm

end OTSelector.Reconstruction

end
end
