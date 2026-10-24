import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerPopulationTypedCostData
import OTSelector.Probability.RNSubplanTypeRefinement

/-!
# Original typed cost data retain a fixed subplan with exact mass

A deterministic original subplan refines the existing types through its original
RN factor. The same cube maps, physical endpoint properties, and uniform cost
constants pass to both flags, without selecting another atlas or sample law.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} {q : ℕ} {cost : X → Y → ℝ}
  (D : PopulationTypedCostData π μ ν T q cost)

/-- The fixed subplan refinement preserves the actual old type geometry and both
original physical populations, with the same constants for every sample size. -/
def refineSubplan (η : Measure (X × Y)) (hη : η ≤ π) :
    PopulationTypedCostData π μ ν (Bool × T) q cost where
  types := D.types.rnSubplanTypes η hη
  sum_eq := D.types.rnSubplanTypes_sum_eq η hη D.sum_eq
  sourceCoordinate t := D.sourceCoordinate t.2
  targetCoordinate t := D.targetCoordinate t.2
  measurable_sourceCoordinate t := D.measurable_sourceCoordinate t.2
  measurable_targetCoordinate t := D.measurable_targetCoordinate t.2
  common_coordinate t := by
    rw [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.target,
      Measure.map_map (D.measurable_sourceCoordinate t.2) measurable_fst,
      Measure.map_map (D.measurable_targetCoordinate t.2) measurable_snd]
    exact Measure.map_congr (ae_mono (D.types.rnSubplanTypes_component_le η hη t)
      (D.paired_coordinate t.2))
  paired_coordinate t := ae_mono (D.types.rnSubplanTypes_component_le η hη t)
    (D.paired_coordinate t.2)
  quadraticConstant := D.quadraticConstant
  globalBound := D.globalBound
  quadratic_nonneg := D.quadratic_nonneg
  bound_nonneg := D.bound_nonneg
  measurable_cost := D.measurable_cost
  global_bounds := D.global_bounds
  sourceGood t := D.sourceGood t.2
  targetGood t := D.targetGood t.2
  source_good t := ae_mono
    (Measure.map_mono (D.types.rnSubplanTypes_component_le η hη t) measurable_fst)
      (D.source_good t.2)
  target_good t := ae_mono
    (Measure.map_mono (D.types.rnSubplanTypes_component_le η hη t) measurable_snd)
      (D.target_good t.2)
  quadratic t := D.quadratic t.2

/-- The selected refined raw type masses are the prescribed original subplan mass. -/
theorem refineSubplan_selected_mass (η : Measure (X × Y)) (hη : η ≤ π) :
    (∑ t, ((D.refineSubplan η hη).types.component (true, t)) univ) = η univ :=
  D.types.rnSubplanTypes_selected_mass η hη D.sum_eq

/-- Selected marks include both the original subplan flag and the old actual type. -/
def selectedSubplanTags : Finset (Option (Bool × T)) :=
  Finset.univ.image (fun t : T ↦ some (true, t))

/-- Flagging a fixed original subplan does not multiply the number of selected cells. -/
theorem card_selectedSubplanTags :
    (selectedSubplanTags (T := T)).card = Fintype.card T := by
  rw [selectedSubplanTags, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro s t h
    exact (Prod.mk.inj (Option.some.inj h)).2

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]

omit [IsFiniteMeasure ν] in
/-- The common type-coordinate probabilities preserve the exact fixed subplan
mass used in the one-permutation attributed-energy estimate. -/
theorem refineSubplan_selected_coordinate_mass (η : Measure (X × Y)) (hη : η ≤ π) :
    (∑ tag ∈ selectedSubplanTags (T := T),
      (D.refineSubplan η hη).coordinateLaw.real {x | x.1 = tag}) = (η univ).toReal := by
  let R := D.refineSubplan η hη
  have hm (t : T) : R.coordinateLaw {x | x.1 = some (true, t)} =
      R.types.component (true, t) univ := by
    have he : {x : Option (Bool × T) × DyadicUnitCube q | x.1 = some (true, t)} =
        ({some (true, t)} ×ˢ univ) := by ext p; simp
    rw [he]
    exact R.types.typeCoordinateLaw_type_mass (μ := μ) R.sourceCoordinate
      (cubeOrigin (q := q)) R.measurable_sourceCoordinate (true, t)
  rw [selectedSubplanTags, Finset.sum_image]
  · change (∑ t, (R.coordinateLaw {x | x.1 = some (true, t)}).toReal) = (η univ).toReal
    calc
      _ = ∑ t, (R.types.component (true, t) univ).toReal := by
        apply Finset.sum_congr rfl
        intro t _
        exact congrArg ENNReal.toReal (hm t)
      _ = (∑ t, R.types.component (true, t) univ).toReal :=
        (ENNReal.toReal_sum (fun t _ ↦ measure_ne_top (R.types.component (true, t)) univ)).symm
      _ = (η univ).toReal := congrArg ENNReal.toReal (D.refineSubplan_selected_mass η hη)
  · intro s _ t _ h
    exact (Prod.mk.inj (Option.some.inj h)).2

end OTSelector.Reconstruction.PopulationTypedCostData
