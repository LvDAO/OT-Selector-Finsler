import OTSelector.Probability.RadonNikodymMarkCoarsening
import OTSelector.Probability.RadonNikodymMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalPartialMarkCoarsening.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalPartialMarkCoarsening`; the selected original proof blocks follow. -/
section

/-!
# Probability.PartialMarkCoarsening

## Lemma skeleton

* **Conditions:** Finite original component measures dominated in sum by the original law, and a partial map between finite mark sets.
* **Objects:** Erasing selected fine tags yields exactly the prescribed retained/coarsened marked experiment.
* **Proof detail:** First group marks along the partial readout, then flatten the nested Option tag; erased fine components and the original unmarked complement combine into the new residual None component.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Finite tagged-measure algebra preserving original residual mass, not a new thinning theorem.
-/

/-! Erasing unwanted fine marks retains the exact prescribed subpopulation experiment. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- An explicit `none` component can be merged into the existing unused original mass. -/
theorem finiteRNMarkLaw_map_join {X U : Type*} [MeasurableSpace X] [Fintype U]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    [MeasurableSpace (Option (Option U))] [MeasurableSingletonClass (Option (Option U))]
    (μ : Measure X) [IsFiniteMeasure μ]
    (k : Option U → Measure X) [∀ u, IsFiniteMeasure (k u)] (hk : ∑ u, k u ≤ μ) :
    (finiteRNMarkLaw μ k).map (fun p ↦ (p.1, p.2.join)) =
      finiteRNMarkLaw μ (fun u ↦ k (some u)) := by
  classical
  let read := fun p : X × Option (Option U) ↦ (p.1, p.2.join)
  have hm : Measurable read := measurable_fst.prodMk
    ((measurable_of_countable Option.join).comp measurable_snd)
  have hmap (ν : Measure X) (tag : Option (Option U)) :
      (ν.map (fun x ↦ (x, tag))).map read = ν.map (fun x ↦ (x, tag.join)) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, tag)) from
      measurable_id.prodMk measurable_const)]
    rfl
  have hremain : μ - ∑ u, k (some u) = (μ - ∑ u, k u) + k none := by
    calc
      _ = ((μ - ∑ u, k u) + ∑ u, k u) - ∑ u, k (some u) := by
        rw [Measure.sub_add_cancel_of_le hk]
      _ = ((μ - ∑ u, k u) + k none + ∑ u, k (some u)) - ∑ u, k (some u) := by
        conv_lhs => arg 1; arg 2; rw [Fintype.sum_option]
        rw [add_assoc]
      _ = _ := Measure.add_sub_cancel
  change (finiteRNMarkLaw μ k).map read = _
  rw [finiteRNMarkLaw, Measure.map_add _ _ hm, Measure.map_finset_sum' hm.aemeasurable]
  simp_rw [hmap]
  rw [Fintype.sum_option, finiteRNMarkLaw, hremain,
    Measure.map_add _ _ (show Measurable (fun x : X ↦ (x, (none : Option U))) from
      measurable_id.prodMk measurable_const)]
  simp only [Option.join_none, Option.join_some, Fintype.sum_option, add_assoc]

/-- Partial finite coarsening keeps selected old marks and sends all other fine marks to none.
The unused original mass changes by exactly those erased components. -/
theorem finiteRNMarkLaw_map_partial {X T U : Type*} [MeasurableSpace X]
    [Fintype T] [Fintype U]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option U)] [MeasurableSingletonClass (Option U)]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hmass : ∑ t, m t ≤ μ)
    (read : T → Option U) :
    (finiteRNMarkLaw μ m).map (fun p ↦ (p.1, p.2.bind read)) =
      finiteRNMarkLaw μ (fun u ↦ groupedMarkComponent m read (some u)) := by
  classical
  letI : MeasurableSpace (Option (Option U)) := ⊤
  letI : MeasurableSingletonClass (Option (Option U)) := ⟨fun _ ↦ trivial⟩
  let k := groupedMarkComponent m read
  have hk : ∑ u, k u ≤ μ := by rwa [sum_groupedMarkComponent]
  letI : ∀ u, IsFiniteMeasure (k u) := fun u ↦ isFiniteMeasure_of_le μ
    ((Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ u)).trans hk)
  have hread : Measurable (fun p : X × Option T ↦ (p.1, p.2.map read)) :=
    measurable_fst.prodMk ((measurable_of_countable (Option.map read)).comp measurable_snd)
  have hjoin : Measurable (fun p : X × Option (Option U) ↦ (p.1, p.2.join)) :=
    measurable_fst.prodMk ((measurable_of_countable Option.join).comp measurable_snd)
  have h := congrArg (fun ν : Measure (X × Option (Option U)) ↦
      ν.map (fun p ↦ (p.1, p.2.join))) (finiteRNMarkLaw_map_coarsen μ m read)
  rw [Measure.map_map hjoin hread, finiteRNMarkLaw_map_join μ k hk] at h
  convert h using 1
  congr 1
  funext p
  rcases p with ⟨x, tag⟩
  cases tag <;> rfl

end OTSelector.Reconstruction

end
end
