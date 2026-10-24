import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellGoodMarkObservation
import OTSelector.Reconstruction.FinslerPopulationTypedCostData

/-! The original-T good hierarchy reads actual old coordinates from the same fine experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Read the old coordinate only from a good retained fine mark. -/
def populationFineGoodCoordinate {X Z C T : Type*} (coord : T → X → Z) (origin : Z)
    (p : X × Option (CellRefinedType C T)) : Option T × Z :=
  populationTypedCoordinate coord origin (p.1, p.2.bind cellRefinedGoodType)

theorem measurable_populationFineGoodCoordinate {X Z C T : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (coord : T → X → Z) (origin : Z) (hm : ∀ t, Measurable (coord t)) :
    Measurable (populationFineGoodCoordinate (C := C) coord origin) := by
  apply (measurable_populationTypedCoordinate coord origin hm).comp
  exact measurable_fst.prodMk ((measurable_of_countable
    (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedGoodType)).comp measurable_snd)

namespace PopulationTypedCostData
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))

/-- Every good pairing component retains its original old-type geometric properties. -/
theorem rnCellGoodTypes_component_le_old (t : T) :
    (D.types.rnCellGoodTypes η hη good bad hsplit).component t ≤ D.types.component t := by
  rw [PopulationSubcouplingTypes.rnCellGoodTypes_component]
  exact ((Measure.le_add_right (le_refl (good t))).trans_eq (hsplit t)).trans
    (D.types.rnSubplanTypes_component_le η hη (false, t))

/-- Paired original coordinates give the good source/target common coordinate law internally. -/
theorem rnCellGoodTypes_common_coordinate (t : T) :
    let G := D.types.rnCellGoodTypes η hη good bad hsplit
    (G.source t).map (D.sourceCoordinate t) = (G.target t).map (D.targetCoordinate t) := by
  dsimp only
  rw [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.target,
    Measure.map_map (D.measurable_sourceCoordinate t) measurable_fst,
    Measure.map_map (D.measurable_targetCoordinate t) measurable_snd]
  exact Measure.map_congr (ae_mono (D.rnCellGoodTypes_component_le_old η hη good bad hsplit t)
    (D.paired_coordinate t))

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- The good hierarchy reads its entire coordinate array from the original fine sample. -/
theorem rnCellRefinedTypes_good_coordinate_joint_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let G := D.types.rnCellGoodTypes η hη good bad hsplit
    let L := G.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ populationFineGoodCoordinate D.sourceCoordinate
            (cubeOrigin (q := q)) (sample i))
          (fun sample j ↦ populationFineGoodCoordinate D.targetCoordinate
            (cubeOrigin (q := q)) (sample j))) =
      (Measure.pi (fun _ : I ↦ L)).prod (Measure.pi (fun _ : J ↦ L)) := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let G := D.types.rnCellGoodTypes η hη good bad hsplit
  let dropX := fun sample : I → X × Option (CellRefinedType C T) ↦
    fun i ↦ ((sample i).1, (sample i).2.bind cellRefinedGoodType)
  let dropY := fun sample : J → Y × Option (CellRefinedType C T) ↦
    fun j ↦ ((sample j).1, (sample j).2.bind cellRefinedGoodType)
  let readX := fun sample : I → X × Option T ↦
    fun i ↦ populationTypedCoordinate D.sourceCoordinate (cubeOrigin (q := q)) (sample i)
  let readY := fun sample : J → Y × Option T ↦
    fun j ↦ populationTypedCoordinate D.targetCoordinate (cubeOrigin (q := q)) (sample j)
  have hdropX : Measurable dropX := measurable_pi_lambda _ (fun i ↦
    (((measurable_pi_apply i).fst).prodMk ((measurable_of_countable
      (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedGoodType)).comp
        (measurable_pi_apply i).snd)))
  have hdropY : Measurable dropY := measurable_pi_lambda _ (fun j ↦
    (((measurable_pi_apply j).fst).prodMk ((measurable_of_countable
      (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedGoodType)).comp
        (measurable_pi_apply j).snd)))
  have hreadX : Measurable readX := measurable_pi_lambda _ (fun i ↦
    (measurable_populationTypedCoordinate _ _ D.measurable_sourceCoordinate).comp
      (measurable_pi_apply i))
  have hreadY : Measurable readY := measurable_pi_lambda _ (fun j ↦
    (measurable_populationTypedCoordinate _ _ D.measurable_targetCoordinate).comp
      (measurable_pi_apply j))
  have h := congrArg (fun ρ ↦ ρ.map (Prod.map readX readY))
    (D.types.rnCellRefinedTypes_iid_good_law (I := I) (J := J) η hη good bad hsplit hπ)
  rw [Measure.map_map (hreadX.prodMap hreadY) (hdropX.prodMap hdropY)] at h
  exact h.trans (G.iid_type_coordinate_law hπ D.sourceCoordinate D.targetCoordinate
    (cubeOrigin (q := q)) D.measurable_sourceCoordinate D.measurable_targetCoordinate
      (D.rnCellGoodTypes_common_coordinate η hη good bad hsplit))

end PopulationTypedCostData
end OTSelector.Reconstruction
