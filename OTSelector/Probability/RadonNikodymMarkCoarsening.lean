import OTSelector.Probability.RadonNikodymMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkCoarsening.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkCoarsening`; the selected original proof blocks follow. -/
section

/-!
# Probability.RadonNikodymMarkCoarsening

## Lemma skeleton

* **Conditions:** Finite component families and a coarsening map of finite tags; the iid form uses finite base/component measures.
* **Objects:** Grouping preserves the total and exact old RN-marked law, including finite iid products.
* **Proof detail:** Sum component measures over coarsening fibers, evaluate the tagged-law rectangles, and commute the coordinatewise tag map with finite products.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (composition): Finite mark coarsening for the actual constructed law; no disjoint physical component supports are needed.
-/

/-! Finite original component refinements preserve the exact old marked law. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- Aggregate finite components along a prescribed old-type observation. -/
def groupedMarkComponent {X T U : Type*} [MeasurableSpace X] [Fintype T]
    (m : T → Measure X) (coarsen : T → U) (u : U) : Measure X :=
  ∑ t ∈ Finset.univ.filter (fun t ↦ coarsen t = u), m t

theorem sum_groupedMarkComponent {X T U : Type*} [MeasurableSpace X]
    [Fintype T] [Fintype U] (m : T → Measure X) (coarsen : T → U) :
    (∑ u, groupedMarkComponent m coarsen u) = ∑ t, m t := by
  classical
  exact Finset.sum_fiberwise Finset.univ coarsen m

/-- Coarsening the fine finite RN marks gives precisely the finite RN law of
the grouped original components, including the same unused mass. -/
theorem finiteRNMarkLaw_map_coarsen
    {X T U : Type*} [MeasurableSpace X] [Fintype T] [Fintype U]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (μ : Measure X) (m : T → Measure X) (coarsen : T → U) :
    (finiteRNMarkLaw μ m).map (fun p ↦ (p.1, p.2.map coarsen)) =
      finiteRNMarkLaw μ (groupedMarkComponent m coarsen) := by
  classical
  let read := fun p : X × Option T ↦ (p.1, p.2.map coarsen)
  have hm : Measurable read := measurable_fst.prodMk
    ((measurable_of_countable (Option.map coarsen)).comp measurable_snd)
  have hmap (ν : Measure X) (t : T) :
      (ν.map (fun x ↦ (x, some t))).map read = ν.map (fun x ↦ (x, some (coarsen t))) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, some t)) from
      measurable_id.prodMk measurable_const)]
    rfl
  have hnone (ν : Measure X) :
      (ν.map (fun x ↦ (x, (none : Option T)))).map read =
        ν.map (fun x ↦ (x, (none : Option U))) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, (none : Option T))) from
      measurable_id.prodMk measurable_const)]
    rfl
  change (finiteRNMarkLaw μ m).map read = _
  rw [finiteRNMarkLaw, Measure.map_add _ _ hm, Measure.map_finset_sum' hm.aemeasurable,
    hnone, finiteRNMarkLaw, sum_groupedMarkComponent]
  simp_rw [hmap]
  congr 1
  rw [← Finset.sum_fiberwise Finset.univ coarsen (fun t ↦ (m t).map (fun x ↦ (x, some (coarsen t))))]
  apply Finset.sum_congr rfl
  intro u _
  rw [groupedMarkComponent, Measure.map_finset_sum
    (show Measurable (fun x : X ↦ (x, some u)) from
      measurable_id.prodMk measurable_const).aemeasurable]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

/-- An explicit componentwise reconstruction removes all new marks from the
full original physical/old-type joint law. -/
theorem finiteRNMarkLaw_map_coarsen_of_components
    {X T U : Type*} [MeasurableSpace X] [Fintype T] [Fintype U]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (μ : Measure X) (fine : T → Measure X) (old : U → Measure X) (coarsen : T → U)
    (hcomponents : ∀ u, groupedMarkComponent fine coarsen u = old u) :
    (finiteRNMarkLaw μ fine).map (fun p ↦ (p.1, p.2.map coarsen)) = finiteRNMarkLaw μ old := by
  rw [finiteRNMarkLaw_map_coarsen]
  congr 1
  exact funext hcomponents

/-- The componentwise old-mark law is preserved on the entire original iid
sample, before any empirical matching or endpoint selection. -/
theorem finiteRNMarkLaw_iid_map_coarsen_of_components
    {X T U J : Type*} [MeasurableSpace X] [Fintype T] [Fintype U] [Fintype J]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (μ : Measure X) [IsFiniteMeasure μ]
    (fine : T → Measure X) [∀ t, IsFiniteMeasure (fine t)]
    (old : U → Measure X) [∀ u, IsFiniteMeasure (old u)] (coarsen : T → U)
    (hcomponents : ∀ u, groupedMarkComponent fine coarsen u = old u) :
    (Measure.pi (fun _ : J ↦ finiteRNMarkLaw μ fine)).map
      (fun sample j ↦ ((sample j).1, (sample j).2.map coarsen)) =
      Measure.pi (fun _ : J ↦ finiteRNMarkLaw μ old) := by
  have hm : Measurable (fun p : X × Option T ↦ (p.1, p.2.map coarsen)) :=
    measurable_fst.prodMk ((measurable_of_countable (Option.map coarsen)).comp measurable_snd)
  rw [Measure.pi_map_pi (fun _ ↦ hm.aemeasurable)]
  simp only [finiteRNMarkLaw_map_coarsen_of_components μ fine old coarsen hcomponents]

end OTSelector.Reconstruction

end
end
