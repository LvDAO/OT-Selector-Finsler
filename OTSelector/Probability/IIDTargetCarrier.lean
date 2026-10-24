import OTSelector.Probability.DirichletReference
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.OriginalTargetCarrier.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.OriginalTargetCarrier`; the selected original proof blocks follow. -/
section

/-!
# Probability.IIDTargetCarrier

## Lemma skeleton

* **Conditions:** An original probability target law carried almost everywhere by any stated set, with finitely many iid targets and an independent auxiliary simplex law.
* **Objects:** Every original target lies in that same carrier almost surely under the actual product law.
* **Proof detail:** Intersect the finitely many coordinate conull events and lift through the auxiliary product measure.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=24): Corollary 252F, p. 24.

Source relation (composition): Finite product carrying statement; no compactness, measurable set or selected endpoint law is additionally asserted.
-/

/-! Original iid targets retain every original full-mass carrier. -/
open Set MeasureTheory
noncomputable section
namespace OTSelector.Probability
variable {M : Type*} [MeasurableSpace M]

/-- Every target in the unchanged iid-targets times Dirichlet-one experiment
lies in an original almost-sure carrier. No topological condition is needed. -/
theorem ae_originalTargets_mem_carrier (n : ℕ) (ν : Measure M)
    [IsProbabilityMeasure ν] (K : Set M) (hν : ∀ᵐ y ∂ν, y ∈ K) :
    ∀ᵐ w ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      ∀ i, w.1 i ∈ K := by
  apply ae_of_ae_map
    (μ := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))
    (p := fun y : Fin (n + 1) → M ↦ ∀ i, y i ∈ K) measurable_fst.aemeasurable
  have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν), ∀ i, y i ∈ K := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (μ := Measure.pi (fun _ : Fin (n + 1) ↦ ν))
      (p := fun y : M ↦ y ∈ K) (measurable_pi_apply i).aemeasurable
    rwa [(measurePreserving_eval (μ := fun _ : Fin (n + 1) ↦ ν) i).map_eq]
  simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hi

end OTSelector.Probability

end
end
