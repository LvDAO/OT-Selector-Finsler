import OTSelector.Reconstruction.FinslerPopulationTypedSubplanData

/-!
# Selected RN marks recover the original physical subplan marginals

For a fixed subplan of the original pairing, forgetting the selected RN marks
returns exactly its original source and target submeasures. The equality keeps
raw mass and the same full original iid population experiment.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A finite injective list of RN marks projects to the sum of its exact original
components, with no normalization by the event probability. -/
theorem finiteRNMarkLaw_restrict_tags_map_fst
    {X T I : Type*} [MeasurableSpace X] [Fintype T] [Fintype I]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (μ : Measure X) [IsFiniteMeasure μ] (m : T → Measure X)
    [∀ t, IsFiniteMeasure (m t)] (tag : I → Option T) (htag : Injective tag) :
    ((finiteRNMarkLaw μ m).restrict {p | ∃ i, p.2 = tag i}).map Prod.fst =
      ∑ i, finiteRNMarkComponent μ m (tag i) := by
  have he : {p : X × Option T | ∃ i, p.2 = tag i} =
      ⋃ i, Prod.snd ⁻¹' {tag i} := by ext p; simp
  have hd : Pairwise (fun i j ↦ Disjoint
      (Prod.snd ⁻¹' {tag i} : Set (X × Option T)) (Prod.snd ⁻¹' {tag j})) := by
    intro i j hij
    apply disjoint_left.mpr
    intro p hp hq
    exact hij (htag (hp.symm.trans hq))
  rw [he, Measure.restrict_iUnion hd (fun i ↦ measurable_snd (measurableSet_singleton _)),
    Measure.sum_fintype, Measure.map_finset_sum' measurable_fst.aemeasurable]
  simp only [finiteRNMarkLaw_restrict_type_map_fst]

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]

/-- The selected marks recover exactly the original source and target subplan
marginals, while the ambient marked experiment still has marginals μ and ν. -/
theorem refineSubplan_selected_physical_laws (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    ((R.types.sourceMarkedLaw μ).restrict
      {p | p.2 ∈ selectedSubplanTags (T := T)}).map Prod.fst = η.map Prod.fst ∧
    ((R.types.targetMarkedLaw ν).restrict
      {p | p.2 ∈ selectedSubplanTags (T := T)}).map Prod.fst = η.map Prod.snd := by
  have htag : Injective (fun t : T ↦ some (true, t)) := by
    intro s t h
    exact (Prod.mk.inj (Option.some.inj h)).2
  have heX : {p : X × Option (Bool × T) |
      p.2 ∈ selectedSubplanTags (T := T)} = {p | ∃ t, p.2 = some (true, t)} := by
    ext p
    simp only [selectedSubplanTags, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, eq_comm]
  have heY : {p : Y × Option (Bool × T) |
      p.2 ∈ selectedSubplanTags (T := T)} = {p | ∃ t, p.2 = some (true, t)} := by
    ext p
    simp only [selectedSubplanTags, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, eq_comm]
  constructor
  · rw [heX, PopulationSubcouplingTypes.sourceMarkedLaw,
      finiteRNMarkLaw_restrict_tags_map_fst μ _ _ htag]
    change (∑ t, ((D.refineSubplan η hη).types.component (true, t)).map Prod.fst) = _
    rw [← Measure.map_finset_sum' measurable_fst.aemeasurable]
    exact congrArg (Measure.map Prod.fst)
      (D.types.rnSubplanTypes_selected_sum_eq η hη D.sum_eq)
  · rw [heY, PopulationSubcouplingTypes.targetMarkedLaw,
      finiteRNMarkLaw_restrict_tags_map_fst ν _ _ htag]
    change (∑ t, ((D.refineSubplan η hη).types.component (true, t)).map Prod.snd) = _
    rw [← Measure.map_finset_sum' measurable_snd.aemeasurable]
    exact congrArg (Measure.map Prod.snd)
      (D.types.rnSubplanTypes_selected_sum_eq η hη D.sum_eq)

end PopulationTypedCostData
end OTSelector.Reconstruction
