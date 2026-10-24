import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCoordinateFacts
import OTSelector.Reconstruction.FinslerRelativeLawOriginalBadCoordinateFacts

/-! Good and bad hierarchy type probabilities retain their literal original subplan masses. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The selected hierarchy types are exactly the present original finite marks. -/
def presentTypeTags (T : Type*) [Fintype T] : Finset (Option T) :=
  Finset.univ.image some

theorem card_presentTypeTags (T : Type*) [Fintype T] :
    (presentTypeTags T).card = Fintype.card T := by
  classical
  rw [presentTypeTags, Finset.card_image_of_injective _ (Option.some_injective T), Finset.card_univ]

namespace PopulationTypedCostData
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]

/-- Good type probabilities are the literal original good component masses. -/
theorem rnCellGoodTypes_coordinate_type_mass (t : T) :
    let G := D.types.rnCellGoodTypes η hη good bad hsplit
    let L := G.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))
    L {p | p.1 = some t} = good t univ := by
  have he : {p : Option T × DyadicUnitCube q | p.1 = some t} = {some t} ×ˢ univ := by
    ext p; simp
  dsimp only
  rw [he, PopulationSubcouplingTypes.typeCoordinateLaw_type_mass _ _ _
    D.measurable_sourceCoordinate, PopulationSubcouplingTypes.rnCellGoodTypes_component]

/-- Bad type probabilities retain each original cell-specific discarded mass. -/
theorem rnCellBadTypes_coordinate_type_mass (t : C × T) :
    let B := D.types.rnCellBadTypes η hη good bad hsplit
    let L := B.typeCoordinateLaw μ (fun t ↦ D.sourceCoordinate t.2) (cubeOrigin (q := q))
    L {p | p.1 = some t} = bad t.1 t.2 univ := by
  have he : {p : Option (C × T) × DyadicUnitCube q | p.1 = some t} = {some t} ×ˢ univ := by
    ext p; simp
  dsimp only
  rw [he]
  have h := (D.types.rnCellBadTypes η hη good bad hsplit).typeCoordinateLaw_type_mass
    (μ := μ) (fun t : C × T ↦ D.sourceCoordinate t.2) (cubeOrigin (q := q))
    (fun t : C × T ↦ D.measurable_sourceCoordinate t.2) t
  rwa [PopulationSubcouplingTypes.rnCellBadTypes_component] at h

/-- The good hierarchy retains |T| selected types and their actual total good mass. -/
theorem rnCellGoodTypes_selected_coordinate_mass :
    let G := D.types.rnCellGoodTypes η hη good bad hsplit
    let L := G.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))
    (∑ tag ∈ presentTypeTags T, L.real {p | p.1 = tag}) = (∑ t, good t univ).toReal := by
  classical
  dsimp only
  rw [presentTypeTags, Finset.sum_image]
  · simp only [measureReal_def, D.rnCellGoodTypes_coordinate_type_mass η hη good bad hsplit]
    apply (ENNReal.toReal_sum _).symm
    intro t _
    have h := measure_ne_top
      ((D.types.rnCellGoodTypes η hη good bad hsplit).component t) univ
    rwa [PopulationSubcouplingTypes.rnCellGoodTypes_component] at h
  · intro s _ t _ h; exact Option.some.inj h

/-- The bad hierarchy's selected mass is the total actual discarded mass, including every cell. -/
theorem rnCellBadTypes_selected_coordinate_mass :
    let B := D.types.rnCellBadTypes η hη good bad hsplit
    let L := B.typeCoordinateLaw μ (fun t ↦ D.sourceCoordinate t.2) (cubeOrigin (q := q))
    (∑ tag ∈ presentTypeTags (C × T), L.real {p | p.1 = tag}) =
      (∑ t : C × T, bad t.1 t.2 univ).toReal := by
  classical
  letI : DecidableEq (C × T) := fun a b ↦ Classical.propDecidable (a = b)
  dsimp only
  rw [presentTypeTags, Finset.sum_image]
  · simp only [measureReal_def, D.rnCellBadTypes_coordinate_type_mass η hη good bad hsplit]
    apply (ENNReal.toReal_sum _).symm
    intro t _
    have h := measure_ne_top
      ((D.types.rnCellBadTypes η hη good bad hsplit).component t) univ
    rwa [PopulationSubcouplingTypes.rnCellBadTypes_component] at h
  · intro s _ t _ h; exact Option.some.inj h

end PopulationTypedCostData
end OTSelector.Reconstruction
